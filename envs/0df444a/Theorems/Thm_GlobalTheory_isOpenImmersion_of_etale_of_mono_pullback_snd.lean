-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_of_etale_of_mono_pullback_snd
-- name    : GlobalTheory.isOpenImmersion_of_etale_of_mono_pullback_snd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:55.698885+00:00
-- url     : https://prove2.me/theorems/f2d11760-09c3-4f39-9705-534e22b11eb9
-- title:
--   Global Theory: is Open Immersion of etale of mono pullback snd
-- statement:
--   The Global Theory construction uses the is Open Immersion of etale of mono pullback snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDominantGeometricPointOfIsPreimmersion.lean#L31-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDominantGeometricPointOfIsPreimmersion.lean#L31-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDominantGeometricPointOfIsPreimmersion
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory

theorem GlobalTheory.isOpenImmersion_of_etale_of_mono_pullback_snd {X U W : Scheme.{0}}
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsDominant j] (q : W ⟶ X) [Etale q] [IsSeparated q]
    [Mono (pullback.snd q j)] : IsOpenImmersion q := by sorry
