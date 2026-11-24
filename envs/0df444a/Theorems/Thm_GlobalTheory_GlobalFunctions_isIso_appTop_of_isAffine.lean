-- Prove2me | Theorems.Thm_GlobalTheory_GlobalFunctions_isIso_appTop_of_isAffine
-- name    : GlobalTheory.GlobalFunctions.isIso_appTop_of_isAffine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:06.169671+00:00
-- url     : https://prove2.me/theorems/2955b83d-4aa1-49c1-950a-ba5c4ab5c951
-- title:
--   Global Functions: is Iso app Top of is Affine
-- statement:
--   The Global Functions construction uses the is Iso app Top of is Affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L316-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L316-L333

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
variable {X S T : Scheme.{0}}

theorem GlobalTheory.GlobalFunctions.isIso_appTop_of_isAffine (hI : FibreInjective) (hD : SmoothDescent) (p : X ⟶ S)
    [IsAffine S] [Smooth p] [IsProper p] [GeometricallyIntegral p] : IsIso p.appTop := by sorry
