-- Prove2me | Theorems.Thm_GaoImpatientMNL_Pricing_proposition_F_5
-- name    : GaoImpatientMNL.Pricing.proposition_F_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:23:53.247068+00:00
-- url     : https://prove2.me/theorems/8fa0a63c-33be-47de-bf20-03eaecdf48c2
-- title:
--   Proposition F.5 — Closed-form relaxation bound
-- statement:
--   Let $T>0$ and $l\ge1$. On $1=q_0\ge q_1\ge\cdots\ge q_l\ge0$, let $R_T^{(l)}$ be the extended-real objective (20), with value $-\infty$ at $q_l=0$, zero entropy term at $q_l=1$, and zero contributions from equal positive neighbors. Write $\widehat z_T^{(l)}$ for its supremum, with $\widehat z_T^{(0)}=0$. Define $G_T(x)=(\sqrt{1+4T/e^x}+1)/2$ for real $x$. Then
--   $$\widehat z_T^{(l)}\le2\log G_T(1)+\frac1{G_T(1+G_T(1)/l)}-1+\frac{G_T(1)}l.$$
--   The bound retains both finite-stage correction terms and applies to every positive integer $l$.
--
--   Differences from the source:
--   - encoding: The finite vector q_0,...,q_l with q_0=1 → A sequence of real numbers with constraints only through l and later entries ignored; reason: Every finite vector has an extension and all objectives depend only on the displayed finite coordinates.
--   - reading: The formulas (19)-(22) on the closed monotone region → EReal values, zero for zero drops, minus infinity for a positive drop with zero endpoint or zero stage mass; R is minus infinity at q_l=0 and has zero entropy term at q_l=1; reason: The source invokes the limit x log x=0 in F.1 and explicitly assigns R^(1)(0)=-infinity in F.2; no boundary point is removed.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, Proposition F.5, PDF p.49, printed p.ec12, held source.pdf.

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Relaxation

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
END IMPORTED LEAN FOR BLIND AUDIT -/

namespace GaoImpatientMNL.Pricing

theorem proposition_F_5 (T : ℝ) (hT : 0 < T) (l : ℕ) (hl : 0 < l) :
    relaxationValue T l ≤
      ((2 * Real.log (G T 1) + 1 / G T (1 + G T 1 / (l : ℝ)) - 1 +
        G T 1 / (l : ℝ) : ℝ) : EReal) := by sorry

end GaoImpatientMNL.Pricing
