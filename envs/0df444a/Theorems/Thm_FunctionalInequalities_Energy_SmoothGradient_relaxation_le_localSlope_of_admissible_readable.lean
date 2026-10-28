-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_relaxation_le_localSlope_of_admissible_readable
-- name    : FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope_of_admissible_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:55.103847+00:00
-- url     : https://prove2.me/theorems/4a182de1-2cd4-4b8f-aff6-7ea50dd1dfcc
-- title:
--   Smooth Relaxation Bound for Admissible Local-Slope Tests
-- statement:
--   This statement extends the local-slope recovery bound from globally Lipschitz tests to all admissible tests.
--
--   Let $V$ be a finite-dimensional real inner-product space with complete Borel measurable and second-countable structure, and let $\nu$ be a probability measure on $V$. Let $g:V\to\mathbb R$ satisfy `LocalSlope.Admissible ν g`, which supplies the admissibility, local Lipschitz regularity, $L^2(\nu)$ membership, measurability, and finite local-slope energy required by the definition.
--
--   Then
--
--   $$
--   \operatorname{relaxation}(\nu)([g]_{L^2(\nu)})
--   \leq
--   \operatorname{LocalSlope.energy}(\nu,g).
--   $$
--
--   The energies are $[0,\infty]$-valued, and the admissibility hypothesis in particular ensures the relevant $L^2$ representative is available. This is the general density estimate for the local-slope energy.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.SmoothGradient`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem relaxation_le_localSlope_of_admissible (ν : ProbabilityMeasure V) {g : V → ℝ}
--       (hg : LocalSlope.Admissible ν g) :
--       relaxation ν (hg.memLp_two.toLp g) ≤ LocalSlope.energy ν g
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Density`](https://prove2.me/theorems/5367291c-d0c5-48f5-b722-92a892987587).
--
--   Definition modules: [`Energy/LocalSlope/Basic`](https://prove2.me/theorems/403376af-90fc-4aef-aed0-aefc10593586), [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Energy/SmoothGradient/Basic`](https://prove2.me/theorems/230d76a3-8a28-41f5-a6c8-38e17a1abcdd).
--
--   Selected supporting theorems: [`apply_mul_le`](https://prove2.me/theorems/bf9de844-4401-433d-8497-f00f6238df47), [`lowerSemicontinuous_secant`](https://prove2.me/theorems/fd7d5e26-5f7d-4c26-af0b-4d2fd37844d8), [`lowerSemicontinuous_sequentialRelaxation`](https://prove2.me/theorems/17428d33-0be2-4fb1-81de-28e6c75ce12e), [`relaxation_le_localSlope_of_lipschitzWith`](https://prove2.me/theorems/56be8628-41c6-4a74-81ac-de10156e3c1f), [`exists_lipschitzWith_of_eq_zero_outside_ball`](https://prove2.me/theorems/edf2acd8-cdce-45dd-bafd-8681d2aeaf30).
--
--   Previous: [`sq_add_le_mul_sq_add`](https://prove2.me/theorems/86a67822-cd23-4fcb-bf30-f85ab83dd686).
--
--   [Source excerpt, lines 1016–1018](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L1016-L1018) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L1013-L1187 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope_of_admissible`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density

open MeasureTheory Filter Topology Set
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope_of_admissible_readable (ν : ProbabilityMeasure V) {g : V → ℝ}
    (hg : LocalSlope.Admissible ν g) :
    relaxation ν (hg.memLp_two.toLp g) ≤ LocalSlope.energy ν g := by sorry
