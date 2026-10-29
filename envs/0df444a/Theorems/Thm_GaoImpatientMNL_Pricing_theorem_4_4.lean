-- Prove2me | Theorems.Thm_GaoImpatientMNL_Pricing_theorem_4_4
-- name    : GaoImpatientMNL.Pricing.theorem_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:24:46.468595+00:00
-- url     : https://prove2.me/theorems/e9f93288-d1e4-4dbb-835e-698a3c6fc8b1
-- title:
--   Theorem 4.4 — 87.8% approximation for joint pricing and assortment optimization
-- statement:
--   Let $n,m\ge1$, let $\alpha\in\mathbb R^n$, let $\beta>0$ be common to all products, and let $1=\lambda_1\ge\cdots\ge\lambda_m>0$. Feasible sequences $S\in\mathcal F$ have pairwise disjoint assortments, allowing empty stages and omitted products. Write $\Pi(p,S)$ for the sequential revenue defined by the model, with every product price unrestricted in $\mathbb R$. Let $T=\sum_i e^{\alpha_i}$ and let $W$ denote the nonnegative principal Lambert function. The first-stage heuristic offers all products immediately and charges
--   $$p_i^H=\frac{1+W(T/e)}\beta\quad(i\in N).$$
--   Both the joint and first-stage revenue maxima exist and are finite, and the joint maximum is positive. The first-stage revenue is exactly the published single-stage MNL revenue for every real price vector. The root specification $W(T/e)\ge0$, $W(T/e)e^{W(T/e)}=T/e$ and uniqueness among nonnegative roots hold. The displayed heuristic attains the first-stage maximum, whose value is $W(T/e)/\beta$. Finally,
--   $$\max_{p\in\mathbb R^n}\Pi(p,N,\varnothing,\ldots,\varnothing)\ge\frac{439}{500}\max_{(p,S)\in\mathbb R^n\times\mathcal F}\Pi(p,S).$$
--   Equivalently, the heuristic revenue dominates $439/500$ times the revenue of every feasible joint decision. The exact rational constant and the full real price domain are retained; no universal numerical lower bound on $H$ is assumed.
--
--   Differences from the source:
--   - encoding: Products and stages numbered from one → Products and stages are Fin n and Fin m, numbered from zero; reason: This is a bijective reindexing; n and m are positive, and empty stages and omitted products remain feasible.
--   - encoding: Common price sensitivity beta → Explicit beta > 0; reason: This is the economic price-sensitivity convention used in Appendix C and the rescaling in Appendix F; intrinsic utilities and input prices remain arbitrary reals.
--   - encoding: Maximum revenues of Pricing-Assortment and the first-stage problem → Real suprema with nonempty bounded ranges, attainment of both values, and positive joint optimum asserted in the conclusion; reason: These well-posedness assertions ensure that the real suprema are exactly the source maxima, rather than default values.
--   - encoding: The optimal first-stage value and its optimizer are described in Appendix F, ec13 → The explicit Lambert price, its optimality, root specification, and revenue identity accompany the max-versus-max inequality; reason: These source-supported identities expose the actual heuristic and prevent an arbitrary optimum or Lambert default from replacing it.
--   - encoding: Decimal 0.878 → Exact real rational 439/500; reason: The numbers are exactly equal; no rounding or weakened guarantee is used.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, Theorem 4.4, PDF p.16, printed p.16, held source.pdf.

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Heuristic

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

open scoped BigOperators
noncomputable section
namespace GaoImpatientMNL.Pricing
def totalAttraction {n : ℕ} (α : Fin n → ℝ) : ℝ := ∑ i, Real.exp (α i)
def stageAttraction {n m : ℕ} (α : Fin n → ℝ) (S : Fin m → Finset (Fin n))
    (k : Fin m) : ℝ := ∑ i ∈ S k, Real.exp (α i)
def QFeasible (l : ℕ) (q : ℕ → ℝ) : Prop :=
  q 0 = 1 ∧ ∀ k < l, 0 ≤ q (k + 1) ∧ q (k + 1) ≤ q k
def stageQ {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (ρ : Fin m → ℝ) (t : ℕ) : ℝ :=
  1 / (1 + ∑ k ∈ Finset.univ.filter (fun k => k.val < t),
    Real.exp (-β * ρ k) * stageAttraction α S k)
def recoveredPrice (β A a b : ℝ) : Option ℝ :=
  if 0 < β ∧ 0 < A ∧ 0 < b ∧ b < a then
    some ((Real.log A - Real.log (1 / b - 1 / a)) / β) else none
def relaxedStage (A a b : ℝ) : EReal :=
  if a = b then 0 else if A ≤ 0 ∨ b ≤ 0 ∨ a ≤ b then ⊥ else
    ((a - b) * (Real.log A - Real.log (1 / b - 1 / a)) : ℝ)
def infinitePatienceRevenue {n m : ℕ} (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (q : ℕ → ℝ) : EReal :=
  ∑ k : Fin m, relaxedStage (stageAttraction α S k) (q k.val) (q (k.val + 1))
def patienceQRevenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (q : ℕ → ℝ) : EReal :=
  if 0 < β then ∑ k : Fin m,
    (↑(lam k / β) : EReal) * relaxedStage (stageAttraction α S k) (q k.val) (q (k.val + 1))
  else ⊥
def relaxationReal (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range l, (q k - q (k + 1)) * Real.log (q k * q (k + 1))) +
    if q l = 1 then 0 else (1 - q l) * Real.log (T / (1 - q l))
def relaxation (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : EReal :=
  if q l = 0 then ⊥ else (relaxationReal T l q : EReal)
def relaxationValue (T : ℝ) (l : ℕ) : EReal :=
  if l = 0 then 0 else sSup {r | ∃ q, QFeasible l q ∧ r = relaxation T l q}
def IsRelaxationMax (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : Prop :=
  QFeasible l q ∧ ∀ r, QFeasible l r → relaxation T l r ≤ relaxation T l q
def G (T x : ℝ) : ℝ := (Real.sqrt (1 + 4 * T / Real.exp x) + 1) / 2
end GaoImpatientMNL.Pricing

noncomputable section
namespace SinglePointPricing.Det
def lambertW (x : ℝ) : ℝ :=
  open Classical in
  if h : ∃ w : ℝ, 0 ≤ w ∧ w * Real.exp w = x then Classical.choose h else 0
end SinglePointPricing.Det
end

noncomputable section
namespace GaoImpatientMNL.Pricing
def heuristicPrice {n : ℕ} (α : Fin n → ℝ) (β : ℝ) : Fin n → ℝ :=
  fun _ => (1 + SinglePointPricing.Det.lambertW (totalAttraction α / Real.exp 1)) / β
def H (x : ℝ) : ℝ :=
  if x = 0 then 1 else
    (1 + x) * SinglePointPricing.Det.lambertW (x * (1 + x)) /
      (2 * (1 + x) * Real.log (1 + x) - x)
def minH : ℝ := sInf (H '' Set.Ici 0)
end GaoImpatientMNL.Pricing
END IMPORTED LEAN FOR BLIND AUDIT -/

namespace GaoImpatientMNL.Pricing

theorem theorem_4_4 {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (h : Parameters (n := n) β lam) :
    MaximaExist α β lam ∧ Feasible (firstSequence n m) ∧
    (∀ p, revenue α β lam (firstSequence n m) p = firstRevenue α β p) ∧
    (let w := SinglePointPricing.Det.lambertW (totalAttraction α / Real.exp 1)
     0 ≤ w ∧ w * Real.exp w = totalAttraction α / Real.exp 1 ∧
       ∀ u : ℝ, 0 ≤ u → u * Real.exp u = totalAttraction α / Real.exp 1 → u = w) ∧
    firstRevenue α β (heuristicPrice α β) = firstValue α β ∧
    firstValue α β = SinglePointPricing.Det.lambertW (totalAttraction α / Real.exp 1) / β ∧
    (439 / 500 : ℝ) * jointValue α β lam ≤ firstValue α β ∧
    (∀ S : Fin m → Finset (Fin n), Feasible S → ∀ p : Fin n → ℝ,
      (439 / 500 : ℝ) * revenue α β lam S p ≤
        revenue α β lam (firstSequence n m) (heuristicPrice α β)) := by sorry

end GaoImpatientMNL.Pricing
