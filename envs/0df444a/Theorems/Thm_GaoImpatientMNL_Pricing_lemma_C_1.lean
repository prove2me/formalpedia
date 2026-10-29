-- Prove2me | Theorems.Thm_GaoImpatientMNL_Pricing_lemma_C_1
-- name    : GaoImpatientMNL.Pricing.lemma_C_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:58.444275+00:00
-- url     : https://prove2.me/theorems/7019ca5e-f81e-48cb-88bd-86c99b437b41
-- title:
--   Lemma C.1 — Nonnegative optimal prices (corrected: offered products)
-- statement:
--   Let $n,m\ge1$, let $\alpha\in\mathbb R^n$, let $\beta>0$ be common to all products, and let $1=\lambda_1\ge\cdots\ge\lambda_m>0$. Feasible sequences $S\in\mathcal F$ have pairwise disjoint assortments, allowing empty stages and omitted products. Write $\Pi(p,S)$ for the sequential revenue defined by the model, with every product price unrestricted in $\mathbb R$. For any fixed feasible $S$ and any global pricing maximizer $p^*$,
--   $$p_i^*\ge0\qquad\text{for every }i\in\bigcup_k S_k.$$
--   Prices of omitted products are unrestricted. This is the offered-product conclusion justified by the source argument.
--
--   Differences from the source:
--   - encoding: Products and stages numbered from one → Products and stages are Fin n and Fin m, numbered from zero; reason: This is a bijective reindexing; n and m are positive, and empty stages and omitted products remain feasible.
--   - encoding: Common price sensitivity beta → Explicit beta > 0; reason: This is the economic price-sensitivity convention used in Appendix C and the rescaling in Appendix F; intrinsic utilities and input prices remain arbitrary reals.
--   - correction: Every optimal price is nonnegative for all products → Every optimal offered-product price is nonnegative; reason: For n=m=1, alpha=0, beta=1, lambda=1 and S_1 empty, every price is optimal with revenue zero, including p_1=-1. Restricting only the conclusion to offered products corrects the false printed claim.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, Lemma C.1, PDF p.39, printed p.ec2, held source.pdf.

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Model

/- BEGIN IMPORTED LEAN FOR BLIND AUDIT
noncomputable section
namespace MultiStoreAssort.Pricing
variable {n : ℕ}
noncomputable def rev14 (a b : Fin n → ℝ) (S : Finset (Fin n)) (p : Fin n → ℝ) : ℝ :=
  (∑ k ∈ S, p k * Real.exp (a k - b k * p k)) / (1 + ∑ k ∈ S, Real.exp (a k - b k * p k))
end MultiStoreAssort.Pricing
end

open scoped BigOperators
noncomputable section
namespace GaoImpatientMNL.Pricing
def Parameters {n m : ℕ} (β : ℝ) (lam : Fin m → ℝ) : Prop :=
  0 < n ∧ 0 < m ∧ 0 < β ∧
    (∀ k, k.val = 0 → lam k = 1) ∧ (∀ k, 0 < lam k) ∧ Antitone lam
def Feasible {n m : ℕ} (S : Fin m → Finset (Fin n)) : Prop :=
  ∀ k h, k ≠ h → Disjoint (S k) (S h)
def attraction {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ)
    (s : Finset (Fin n)) : ℝ := ∑ i ∈ s, Real.exp (α i - β * p i)
def prefixWeight {n m : ℕ} (v : Fin n → ℝ) (S : Fin m → Finset (Fin n)) (k : Fin m) : ℝ :=
  ∑ h ∈ Finset.univ.filter (fun h => h < k), ∑ i ∈ S h, v i
def choiceFormula {n m : ℕ} (v : Fin n → ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (k : Fin m) (i : Fin n) : ℝ :=
  lam k * v i / ((1 + prefixWeight v S k) * (1 + prefixWeight v S k + ∑ j ∈ S k, v j))
def revenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) : ℝ :=
  ∑ k, (lam k * ∑ i ∈ S k, p i * Real.exp (α i - β * p i)) /
    ((1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k) *
      (1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k + attraction α β p (S k)))
def firstSequence (n m : ℕ) : Fin m → Finset (Fin n) :=
  fun k => if k.val = 0 then Finset.univ else ∅
def firstRevenue {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ) : ℝ :=
  MultiStoreAssort.Pricing.rev14 α (fun _ => β) Finset.univ p
def jointRevenues {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ) : Set ℝ :=
  {r | ∃ S : Fin m → Finset (Fin n), Feasible S ∧ ∃ p : Fin n → ℝ, r = revenue α β lam S p}
def jointValue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ) : ℝ :=
  sSup (jointRevenues α β lam)
def firstValue {n : ℕ} (α : Fin n → ℝ) (β : ℝ) : ℝ :=
  sSup (Set.range (firstRevenue α β))
def IsPricingMax {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) : Prop :=
  ∀ p', revenue α β lam S p' ≤ revenue α β lam S p
def MaximaExist {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ) : Prop :=
  (jointRevenues α β lam).Nonempty ∧ BddAbove (jointRevenues α β lam) ∧
  (Set.range (firstRevenue α β)).Nonempty ∧ BddAbove (Set.range (firstRevenue α β)) ∧
  (∃ S p, Feasible S ∧ revenue α β lam S p = jointValue α β lam) ∧
  (∃ p, firstRevenue α β p = firstValue α β) ∧ 0 < jointValue α β lam
end GaoImpatientMNL.Pricing
END IMPORTED LEAN FOR BLIND AUDIT -/

namespace GaoImpatientMNL.Pricing

theorem lemma_C_1 {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (h : Parameters (n := n) β lam) (S : Fin m → Finset (Fin n)) (hS : Feasible S)
    (p : Fin n → ℝ) (hp : IsPricingMax α β lam S p) :
    ∀ k, ∀ i ∈ S k, 0 ≤ p i := by sorry

end GaoImpatientMNL.Pricing
