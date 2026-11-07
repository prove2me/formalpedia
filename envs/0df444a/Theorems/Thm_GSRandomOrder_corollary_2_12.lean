-- Prove2me | Theorems.Thm_GSRandomOrder_corollary_2_12
-- name    : GSRandomOrder.corollary_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:50.975209+00:00
-- url     : https://prove2.me/theorems/3e935bae-219a-4f2f-9983-e26f8bffb774
-- title:
--   Corollary 2.12 — from inclusion to value
-- statement:
--   Let $v$ be a GS valuation and let $X\in\operatorname{dom}v$ satisfy $v(X)\ge v(Y)$ for every $Y\subseteq X$. Let $A$ be a random set such that, almost surely, $A\subseteq D_v(T)$ for some (random) $T$. If $P[g\in A]\ge\rho$ for every $g\in X$, then
--   $$
--   \mathbb E\,v(A)\ge\rho\,v(X).
--   $$
--
--   This is how part (iii) of Theorem 3.1 follows from part (i).
--
--   **Formalization Note** The random set is a map $A:\alpha\to$ `Finset (Fin n)` on a probability space whose events $\{g\in A\}$ are measurable. $v(A)$ and $v(X)$ are read as real numbers; this is exact because $v(X)>-\infty$ and $A$ lies almost surely in a canonical demand, hence in $\operatorname{dom}v$.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: a random set A and E v(A) → A : α → Finset (Fin n) with every {g ∈ A} measurable; E v(A) = ∫ (v (A ω)).unbotD 0 ∂P; reason: a random finite set is measurable iff its membership events are; v(A) is a.s. finite by the hypothesis and Lemma 2.10(b)
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Corollary 2.12, p.9

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_canonicalDemand

set_option autoImplicit false

open MeasureTheory

namespace GSRandomOrder

/-- **Corollary 2.12 (From inclusion to value)** (Paes Leme, Pál, Patel, *Gross Substitutes
Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §2.3, p.9). Let `v`
be a GS valuation, let `X` be as in Lemma 2.11 (`X ∈ dom v` and `v(X) ≥ v(Y)` for every
`Y ⊆ X`), and let `A` be a random set such that, almost surely, `A ⊆ D_v(T)` for some (random)
`T`. If `P[g ∈ A] ≥ ρ` for every `g ∈ X`, then `E v(A) ≥ ρ v(X)`.

**Formalization Note.** The random set is `A : α → Finset (Fin n)` on a probability space
`(α, P)`, measurable in the sense that every event `{g ∈ A}` is measurable. `v(X)` and `v(A)`
are read as real numbers with `unbotD 0`; this is exact, because `v X ≠ ⊥` is assumed and `A` lies
almost surely in a canonical demand, hence in `dom v` (Lemma 2.10(b)), so `v(A)` is almost surely
finite and the expectation is that of the finite random variable `v(A)`. `ρ` is any real number. -/
theorem corollary_2_12 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (X : Finset (Fin n)) (hX : v X ≠ ⊥) (hmax : ∀ Y ⊆ X, v Y ≤ v X)
    {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (A : α → Finset (Fin n)) (hAmeas : ∀ g : Fin n, MeasurableSet {ω | g ∈ A ω})
    (hAD : ∀ᵐ ω ∂P, ∃ T : Finset (Fin n), A ω ⊆ canonicalDemand v T)
    (ρ : ℝ) (hρ : ∀ g ∈ X, ρ ≤ (P {ω | g ∈ A ω}).toReal) :
    ρ * (v X).unbotD 0 ≤ ∫ ω, (v (A ω)).unbotD 0 ∂P := by sorry

end GSRandomOrder
