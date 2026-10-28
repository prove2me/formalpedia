-- Prove2me | Theorems.Thm_OAI_CubicTorus_TrueRadialTube_revolution_area_le_perimeter
-- name    : OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:51:21.886005+00:00
-- url     : https://prove2.me/theorems/0bccd10d-64a8-458a-b6fe-21588d5d1392
-- title:
--   OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter` of [lean/OAI/Geometry/CubicTorus/Reflection/DelaunayPeriodicMoments.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/DelaunayPeriodicMoments.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem TrueRadialTube.revolution_area_le_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
--       (hangle : ∀ t a,r (t,a)=r (t,0)) :
--       2*Real.pi*(∫ t in (0 : ℝ)..1,r (t,0)*Real.sqrt (1+(deriv (fun u => r (u,0)) t)^2))≤
--         (perimeter E).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere` and `OAI.CubicTorus.TrueRadialTube` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.perimeter` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_first_transition_standard` and `OAI.CubicTorus.isMinimizerAt_no_monotone_revolution` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/DelaunayPeriodicMoments.lean (declaration OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter)

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

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem TrueRadialTube.revolution_area_le_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) :
    2*Real.pi*(∫ t in (0 : ℝ)..1,r (t,0)*Real.sqrt (1+(deriv (fun u => r (u,0)) t)^2))≤
      (perimeter E).toReal := by
  sorry

end CubicTorus

end
end

end OAI
end
