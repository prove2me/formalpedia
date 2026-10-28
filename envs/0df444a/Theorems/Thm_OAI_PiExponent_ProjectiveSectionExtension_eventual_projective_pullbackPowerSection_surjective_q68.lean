-- Prove2me | Theorems.Thm_OAI_PiExponent_ProjectiveSectionExtension_eventual_projective_pullbackPowerSection_surjective_q68
-- name    : OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:43:53.125775+00:00
-- url     : https://prove2.me/theorems/8f8e3988-bd01-4d9d-8c02-9f878ea56d51
-- title:
--   OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective` of [lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionPullback.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionPullback.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.ProjectiveSectionExtension`, with `open AlgebraicGeometry CategoryTheory`, `open PiExponentSeshadri.Geometry`, `open PiExponent.GeometrySupport`):
--
--   ```lean
--   theorem eventual_projective_pullbackPowerSection_surjective_q68
--       {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
--       (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
--       ∃ N, ∀ n, N ≤ n → Function.Surjective
--         (pullbackPowerSection (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.ProjectiveO1.projectiveSpace` and `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.ProjectiveO1.lineBundle`, `OAI.PiExponentSeshadri.Geometry.modulePow` and `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.GlobalSections` (definitions bundle `OAIQ068A013` of this split); `OAI.PiExponentSeshadri.Geometry.pullbackPowerSection` (definitions bundle `OAIQ068A028` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.AdmissibleMatrixInterpolation.eventual_packets_of_eventual_jetRestriction_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionPullback.lean (declaration OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective)

import Mathlib
import Definitions.Def_OAIQ068A028

section

attribute [-instance] _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveSectionExtension
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X Y : Scheme.{0}}

theorem eventual_projective_pullbackPowerSection_surjective_q68
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (pullbackPowerSection (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n) := by
  sorry

end PiExponent.ProjectiveSectionExtension
end

end OAI
end
