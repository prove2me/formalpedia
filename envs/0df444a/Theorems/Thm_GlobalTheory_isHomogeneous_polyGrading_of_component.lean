-- Prove2me | Theorems.Thm_GlobalTheory_isHomogeneous_polyGrading_of_component
-- name    : GlobalTheory.isHomogeneous_polyGrading_of_component
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:35.101622+00:00
-- url     : https://prove2.me/theorems/bc75b131-00e3-4873-bcae-7cbe82164c4c
-- title:
--   Global Theory: is Homogeneous poly Grading of component
-- statement:
--   The Global Theory construction uses the is Homogeneous poly Grading of component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormOfCompatibleFractions.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormOfCompatibleFractions.lean#L22-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
open GlobalTheory

theorem GlobalTheory.isHomogeneous_polyGrading_of_component {ι A : Type} [CommRing A]
    (J : Ideal (MvPolynomial ι A))
    (hJ : ∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) :
    (J : Submodule (MvPolynomial ι A) (MvPolynomial ι A)).IsHomogeneous (polyGrading ι A) := by sorry
