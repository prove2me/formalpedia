-- Prove2me | Theorems.Thm_OAI_PiExponent_GeometrySupport_NoetherianAmpleSerreVanishing_ample_power_cohomology_zero_q68
-- name    : OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_power_cohomology_zero_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:22:32.907231+00:00
-- url     : https://prove2.me/theorems/50376db3-1d15-46c1-9275-5ba4a114968a
-- title:
--   OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_power_cohomology_zero_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_power_cohomology_zero` of [lean/OAI/NumberTheory/PiExponent/Cohomology/NoetherianAmpleSerreVanishing.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/NoetherianAmpleSerreVanishing.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective`):
--
--   ```lean
--   theorem ample_power_cohomology_zero_q68
--       (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
--       (L : LineBundle X) (hL : LineBundle.IsAmple X L) :
--       ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
--         ∀ x : cohomology (modulePow X L.sheaf n) q, x = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` and `OAI.PiExponentSeshadri.Geometry.structureSheaf` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.schemeHasExt` (definitions bundle `OAIQ068A003` of this split); `OAI.PiExponentSeshadri.Geometry.modulePow` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponentSeshadri.Geometry.cohomology` (definitions bundle `OAIQ068A022` of this split).
--
--   **Used by.** The proofs of `OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison_q68` and `OAI.PiExponent.NumericalAmpleness.eventual_zeroDivisor_power_cohomology_zero_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/NoetherianAmpleSerreVanishing.lean (declaration OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_power_cohomology_zero)

import Mathlib
import Definitions.Def_OAIQ068A021
import Definitions.Def_OAIQ068A022

section

attribute [-instance] _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem ample_power_cohomology_zero_q68
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : cohomology (modulePow X L.sheaf n) q, x = 0 := by
  sorry

end
end PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing

end OAI
end
