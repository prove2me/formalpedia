-- Prove2me | Theorems.Thm_MFEUnique_Uniq_stochLE_iff_upper_set
-- name    : MFEUnique.Uniq.stochLE_iff_upper_set
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:49.507354+00:00
-- url     : https://prove2.me/theorems/3fa6dd44-5539-45ab-b768-956b49db2e13
-- title:
--   p. 12 (Kamae et al. 1977) — s₁ ⪰SD s₂ if and only if s₁(B) ≥ s₂(B) for every upper set B
-- statement:
--   Let $X$ be a compact metric space with a closed partial order $\ge$ and its Borel $\sigma$-algebra. A Borel set $B \subseteq X$ is an **upper set** if $x_1 \in B$ and $x_2 \ge x_1$ imply $x_2 \in B$. For probability measures $s_1, s_2$ on $X$,
--   $$s_1 \succeq_{SD} s_2 \iff s_1(B) \ge s_2(B) \ \text{ for every Borel upper set } B.$$
--
--   The paper uses this characterization to verify $\succeq_{SD}$ through the probabilities of upper sets, which is how the one-step comparison of the operators $M_s$ is carried out.
--
--   **Formalization Note** $s_1 \succeq_{SD} s_2$ is `StochLE s₂ s₁`: the arguments of `StochLE` are swapped relative to the paper's notation, and its test functions are bounded, measurable and increasing (equivalent to the paper's definition for probability measures).
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, p. 12, paragraph defining ⪰SD and upper sets (citing Kamae, Krengel and O'Brien 1977)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE

open MeasureTheory StochIneqPO.Comparison

namespace MFEUnique.Uniq

/-- p. 12 (citing Kamae et al. 1977): `s₁ ⪰SD s₂` if and only if `s₁(B) ≥ s₂(B)` for every
(Borel) upper set `B`. Here `s₁ ⪰SD s₂` is `StochLE s₂ s₁`. -/
theorem stochLE_iff_upper_set {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    (s₁ s₂ : ProbabilityMeasure X) :
    StochLE (s₂ : Measure X) (s₁ : Measure X) ↔
      ∀ B : Set X, MeasurableSet B → IsUpperSet B → (s₂ : Measure X) B ≤ (s₁ : Measure X) B := by sorry

end MFEUnique.Uniq
