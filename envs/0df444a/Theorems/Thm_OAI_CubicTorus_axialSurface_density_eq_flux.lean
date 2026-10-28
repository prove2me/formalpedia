-- Prove2me | Theorems.Thm_OAI_CubicTorus_axialSurface_density_eq_flux
-- name    : OAI.CubicTorus.axialSurface_density_eq_flux
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:52:10.951242+00:00
-- url     : https://prove2.me/theorems/1a20bd76-60da-43d7-a05f-08a6c4a3fae4
-- title:
--   OAI.CubicTorus.axialSurface_density_eq_flux: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.axialSurface_density_eq_flux` of [lean/OAI/Geometry/CubicTorus/Reflection/ActualAxialFlux.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ActualAxialFlux.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma axialSurface_density_eq_flux {E : Set Torus} (hE : MeasurableSet E)
--       {μ : FiniteMeasure NormalBundle} {H : ℝ}
--       (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
--         H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
--       (fun t ↦ ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal)=ᵐ[volume]
--         actualAxialFlux E μ H i
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.actualAxialFlux`, `OAI.CubicTorus.axialSurfaceMarginal`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.Periodic.Variation` and `OAI.CubicTorus.Periodic.normalFirstVariation` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.axial_integrated_flux_actual`, `OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_flux_unrestricted` and `OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ActualAxialFlux.lean (declaration OAI.CubicTorus.axialSurface_density_eq_flux)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSurface_density_eq_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    (fun t ↦ ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal)=ᵐ[volume]
      actualAxialFlux E μ H i := by
  sorry

end CubicTorus

end
end

end

end OAI
end
