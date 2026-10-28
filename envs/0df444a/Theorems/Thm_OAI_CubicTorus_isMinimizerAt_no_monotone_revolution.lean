-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_no_monotone_revolution
-- name    : OAI.CubicTorus.isMinimizerAt_no_monotone_revolution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:05:56.761662+00:00
-- url     : https://prove2.me/theorems/8036d929-6d9f-425e-978f-a32c99cb778d
-- title:
--   OAI.CubicTorus.isMinimizerAt_no_monotone_revolution: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_no_monotone_revolution` of [lean/OAI/Geometry/CubicTorus/Profiles/FourStarScalarGrid.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FourStarScalarGrid.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_no_monotone_revolution {V : ℝ} (hVhalf : V∈Ioc (0 : ℝ) (1/2))
--       {G : Set Torus} (hG : MeasurableSet G) (hm : IsMinimizerAt V G)
--       {b : Fin 3 → Bool} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube G (chamberCorner b) r)
--       (hangle : ∀ t a,r (t,a)=r (t,0))
--       (heven : ∀ t a,r (-t,a)=r (t,a))
--       (hneg : ∀ t∈Ioo (chamberCorner b 0) (chamberCorner b 0+1/2),
--         deriv (fun s => r (s,0)) t<0) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.TrueRadialTube` and `OAI.CubicTorus.chamberCorner` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FourStarScalarGrid.lean (declaration OAI.CubicTorus.isMinimizerAt_no_monotone_revolution)

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

theorem isMinimizerAt_no_monotone_revolution {V : ℝ} (hVhalf : V∈Ioc (0 : ℝ) (1/2))
    {G : Set Torus} (hG : MeasurableSet G) (hm : IsMinimizerAt V G)
    {b : Fin 3 → Bool} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube G (chamberCorner b) r)
    (hangle : ∀ t a,r (t,a)=r (t,0))
    (heven : ∀ t a,r (-t,a)=r (t,a))
    (hneg : ∀ t∈Ioo (chamberCorner b 0) (chamberCorner b 0+1/2),
      deriv (fun s => r (s,0)) t<0) : False := by
  sorry

end CubicTorus

end
end

end OAI
end
