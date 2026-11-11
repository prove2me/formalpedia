-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_invertible_ideal_s01
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:20.661795+00:00
-- url     : https://prove2.me/theorems/747807dd-f43c-4a64-a1b6-f8dfb3ba4639
-- title:
--   OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal` of [lean/OAI/AlgebraicGeometry/Seshadri/Divisors/IntegralCurveCartier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/IntegralCurveCartier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`):
--
--   ```lean
--   theorem IntegralCurve.invertible_ideal_s01 (S : Surface) (C : IntegralCurve S) :
--       InvertiblePullbackIdeal C.embedding.ker (𝟙 S.scheme)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.InvertiblePullbackIdeal` and `OAI.MaximalSeshadri.Geometry.Surface` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01`, `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` and `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/IntegralCurveCartier.lean (declaration OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem IntegralCurve.invertible_ideal_s01 (S : Surface) (C : IntegralCurve S) :
    InvertiblePullbackIdeal C.embedding.ker (𝟙 S.scheme) := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
