-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_divisible_mixed_extension_s01
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.divisible_mixed_extension_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:04.532496+00:00
-- url     : https://prove2.me/theorems/e1b33688-fa35-4e91-9f1d-9b17bd22ce7f
-- title:
--   OAI.MaximalSeshadri.Geometry.LineBundle.divisible_mixed_extension_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.LineBundle.divisible_mixed_extension` of [lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/MixedDivisibleExtension.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/MixedDivisibleExtension.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite`, `open MaximalSeshadri.Frames MaximalSeshadri.TensorPure`):
--
--   ```lean
--   theorem LineBundle.divisible_mixed_extension_s01 [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
--       (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
--       (w : Γ(M.sheaf,sectionOpen X s)) :
--       ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
--         sectionOpen X t ≤ sectionOpen X s ∧
--         t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
--           pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
--             ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.powerSection` (definitions bundle `Q223SES000` of this split); `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.TensorPure.pure` and `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.modulePow`, `OAI.MaximalSeshadri.Geometry.sectionOpen` and `OAI.MaximalSeshadri.Geometry.structureSheaf` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.coprime_embedding_option_s01` and `OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/MixedDivisibleExtension.lean (declaration OAI.MaximalSeshadri.Geometry.LineBundle.divisible_mixed_extension)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem LineBundle.divisible_mixed_extension_s01 [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t ≤ sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
