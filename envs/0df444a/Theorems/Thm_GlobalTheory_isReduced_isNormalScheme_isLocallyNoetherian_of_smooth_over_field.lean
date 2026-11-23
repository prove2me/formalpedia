-- Prove2me | Theorems.Thm_GlobalTheory_isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
-- name    : GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:48.920035+00:00
-- url     : https://prove2.me/theorems/426ccd54-b9e5-44eb-9331-8828a0f85bb0
-- title:
--   Global Theory: is Reduced is Normal Scheme is Locally Noetherian of smooth over field
-- statement:
--   The Global Theory construction uses the is Reduced is Normal Scheme is Locally Noetherian of smooth over field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo.lean#L24-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s →
      IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X := by sorry
