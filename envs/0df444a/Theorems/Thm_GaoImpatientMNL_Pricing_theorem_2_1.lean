-- Prove2me | Theorems.Thm_GaoImpatientMNL_Pricing_theorem_2_1
-- name    : GaoImpatientMNL.Pricing.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:23:49.618+00:00
-- url     : https://prove2.me/theorems/3b33982a-e21f-4505-bfdc-7f5f00a734a5
-- title:
--   Theorem 2.1 — Choice probabilities
-- statement:
--   Let $n,m\ge1$, and consider the measurable mutually independent Gumbel utilities and finite patience variable of the customer model on any probability space. Product $i$ has location $\mu_i\in\mathbb R$, the one outside utility has location zero, all scales are one, and $P(Y\ge k)=\lambda_k>0$. For every feasible sequence of disjoint assortments, every stage $k$, and every $i\in S_k$, the operational purchase event is measurable and
--   $$P(\text{purchase }i\text{ at stage }k)=\frac{\lambda_k e^{\mu_i}}{(1+\sum_{h<k}\sum_{j\in S_h}e^{\mu_j})(1+\sum_{h\le k}\sum_{j\in S_h}e^{\mu_j})}.$$
--   The event uses one fixed outside draw, requires every earlier product to fail the acceptance test, and chooses a maximum-utility product in the current stage. This connects customer behavior to the objective used in the pricing results.
--
--   Differences from the source:
--   - encoding: Products and stages numbered from one → Products and stages are Fin n and Fin m, numbered from zero; reason: This is a bijective reindexing; n and m are positive, and empty stages and omitted products remain feasible.
--   - encoding: Probabilities of purchases under independent continuous utilities → Measurable purchase events with smallest-index product tie-breaking and ENNReal probabilities; reason: Ties have probability zero; explicit measurability and probability conversion change no source instance. Patience is embedded by its finite real index for mutual independence.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, Theorem 2.1, PDF p.6, printed p.6, held source.pdf.

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Customer

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

noncomputable section
namespace ActuarialValuation
noncomputable def exGumbelMaxCdf (location scale x : ℝ) : ℝ := Real.exp (-Real.exp (-(x-location)/scale))
end ActuarialValuation
end

open MeasureTheory
noncomputable section
namespace GaoImpatientMNL.Pricing
def HasGumbelLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (location scale : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ Measurable X ∧ 0 < scale ∧
    ∀ x, P {ω | X ω ≤ x} = ENNReal.ofReal (ActuarialValuation.exGumbelMaxCdf location scale x)
end GaoImpatientMNL.Pricing

open MeasureTheory ProbabilityTheory
noncomputable section
namespace GaoImpatientMNL.Pricing
def customerFamily {Ω : Type*} {n m : ℕ} (U : Option (Fin n) → Ω → ℝ)
    (Y : Ω → Fin m) : Option (Option (Fin n)) → Ω → ℝ
  | none => fun ω => (Y ω).val
  | some i => U i
def CustomerLaw {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (P : Measure Ω)
    (μ : Fin n → ℝ) (lam : Fin m → ℝ)
    (U : Option (Fin n) → Ω → ℝ) (Y : Ω → Fin m) : Prop :=
  HasGumbelLaw P (U none) 0 1 ∧
  (∀ i, HasGumbelLaw P (U (some i)) (μ i) 1) ∧ Measurable Y ∧
  iIndepFun (customerFamily U Y) P ∧
  (∀ k, P {ω | k ≤ Y ω} = ENNReal.ofReal (lam k)) ∧
  (∀ k, 0 < lam k)
def purchaseEvent {Ω : Type*} {n m : ℕ} (U : Option (Fin n) → Ω → ℝ)
    (Y : Ω → Fin m) (S : Fin m → Finset (Fin n)) (k : Fin m) (i : Fin n) : Set Ω :=
  {ω | i ∈ S k ∧ k ≤ Y ω ∧
    (∀ h, h < k → ∀ j ∈ S h, U (some j) ω ≤ U none ω) ∧
    U none ω < U (some i) ω ∧
    (∀ j ∈ S k, U (some j) ω ≤ U (some i) ω) ∧
    (∀ j ∈ S k, U (some j) ω = U (some i) ω → i ≤ j)}
end GaoImpatientMNL.Pricing
END IMPORTED LEAN FOR BLIND AUDIT -/

namespace GaoImpatientMNL.Pricing

theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (P : MeasureTheory.Measure Ω)
    (μ : Fin n → ℝ) (lam : Fin m → ℝ) (U : Option (Fin n) → Ω → ℝ)
    (Y : Ω → Fin m) (hLaw : CustomerLaw P μ lam U Y)
    (S : Fin m → Finset (Fin n)) (hS : Feasible S)
    (k : Fin m) (i : Fin n) (hi : i ∈ S k) :
    MeasurableSet (purchaseEvent U Y S k i) ∧
    P (purchaseEvent U Y S k i) =
      ENNReal.ofReal (choiceFormula (fun j => Real.exp (μ j)) lam S k i) := by sorry

end GaoImpatientMNL.Pricing
