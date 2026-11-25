-- Prove2me | Theorems.Thm_GlobalTheory_KS_isCob_of_isAffineOpen
-- name    : GlobalTheory.KS.isCob_of_isAffineOpen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:47:59.284129+00:00
-- url     : https://prove2.me/theorems/fbfe4995-70c3-4be3-b12d-be65b9151734
-- title:
--   KS: is Cob of is Affine Open
-- statement:
--   The KS construction uses the is Cob of is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsCobOfIsAffineOpen.lean#L39-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsCobOfIsAffineOpen.lean#L39-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecOn GlobalTheory.AbLaw.CechOne

theorem GlobalTheory.KS.isCob_of_isAffineOpen : ∀ (X : Scheme.{0}) (J : Type) (U : J → X.Opens) (c : C1 U),
    IsAffineOpen (⨆ α, U α) → IsCoc U c → IsCob U c := by sorry
