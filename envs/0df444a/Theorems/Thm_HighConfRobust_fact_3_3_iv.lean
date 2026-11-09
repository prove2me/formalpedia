-- Prove2me | Theorems.Thm_HighConfRobust_fact_3_3_iv
-- name    : HighConfRobust.fact_3_3_iv
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:55.961057+00:00
-- url     : https://prove2.me/theorems/a5b22854-0a40-41a2-bc51-f5b2ab0704b5
-- title:
--   Fact 3.3 (iv) — change of measure under bounded Rényi divergence
-- statement:
--   Let $P,Q$ be probability distributions and $E$ a measurable event.
--
--   1. If $q>1$ and $D_q(P\,\|\,Q)<\infty$, then
--   $$
--   P(E)\le Q(E)^{\frac{q-1}{q}}\exp\Big(\frac{q-1}{q}\,D_q(P\,\|\,Q)\Big).
--   $$
--   2. If $D_1(P\,\|\,Q)<\infty$ and $0<Q(E)<1$, then
--   $$
--   P(E)\le\frac{D_1(P\,\|\,Q)+\log 2}{\log(1/Q(E))}.
--   $$
--   3. If $D_1(P\,\|\,Q)<\infty$ and $Q(E)\in\{0,1\}$, then $P(E)=Q(E)$.
--
--   A small Rényi divergence prevents an event that is rare under $Q$ from being likely under $P$; Theorem 4.2 uses the case $q>1$ to transfer the algorithm's failure probability from a reference law to the contaminated law.
--
--   **Formalization Note** "$D_q(P\,\|\,Q)<\infty$" is encoded by a real number $D$ with $D_q(P\,\|\,Q)\le D$, and the bound is stated with $D$; since the bounds increase with $D$ and $D=D_q(P\,\|\,Q)$ is allowed, this is equivalent. Probabilities are real numbers.
--
--   Differences from the source:
--   - encoding: D_q(P ‖ Q) < ∞ and the bound evaluated at D_q(P ‖ Q) → for every real D with renyiDivergence q P Q ≤ D, the bound evaluated at D; reason: the bounds are increasing in D and D = D_q(P ‖ Q) is admissible when it is finite, so the two forms are equivalent
--   - encoding: q = 1 bound for every measurable E, plus the clause for Q(E) ∈ {0, 1} → q = 1 bound for 0 < Q(E) < 1; clause 3 for Q(E) ∈ {0, 1}; reason: the formula divides by log(1/Q(E)), which is 0 at Q(E) = 1 and +∞ at Q(E) = 0; those two cases are exactly the page's last sentence
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Fact 3.3 (iv), p.16

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence

namespace HighConfRobust

open MeasureTheory

/-- **Fact 3.3 (iv)** (change of measure, p.16). Let `P, Q` be probability measures and `E` a
measurable event.
1. If `q > 1` and `D_q(P ‖ Q) < ∞`, then `P(E) ≤ Q(E)^{(q−1)/q} · exp(((q−1)/q) · D_q(P ‖ Q))`.
2. If `D₁(P ‖ Q) < ∞` and `0 < Q(E) < 1`, then `P(E) ≤ (D₁(P ‖ Q) + log 2) / log(1/Q(E))`.
3. If `D₁(P ‖ Q) < ∞` and `Q(E) ∈ {0, 1}`, then `P(E) = Q(E)`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Fact 3.3 (iv), p.16.

**Formalization Note** "`D_q(P ‖ Q) < ∞`" is encoded by a real number `D` with `D_q(P ‖ Q) ≤ D`; the
bounds are increasing in `D` and `D = D_q(P ‖ Q)` is allowed, so this is equivalent to the bound at
the divergence itself. Probabilities are `(P E).toReal`. The `q = 1` formula is stated for
`0 < Q(E) < 1`, where it is defined; the cases `Q(E) ∈ {0, 1}` are clause 3. -/
theorem fact_3_3_iv {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (E : Set X) (hE : MeasurableSet E) :
    (∀ q D : ℝ, 1 < q → renyiDivergence q P Q ≤ (D : EReal) →
        (P E).toReal ≤ (Q E).toReal ^ ((q - 1) / q) * Real.exp ((q - 1) / q * D)) ∧
    (∀ D : ℝ, renyiDivergence 1 P Q ≤ (D : EReal) → 0 < Q E → Q E < 1 →
        (P E).toReal ≤ (D + Real.log 2) / Real.log (1 / (Q E).toReal)) ∧
    (renyiDivergence 1 P Q ≠ ⊤ → (Q E = 0 ∨ Q E = 1) → P E = Q E) := by sorry

end HighConfRobust
