-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_isAffineOpen_inf_of_isSeparated
-- name    : GlobalTheory.KuennethOne.isAffineOpen_inf_of_isSeparated
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:21.479614+00:00
-- url     : https://prove2.me/theorems/20343b73-d9b8-43d6-b4f6-b7cef3e17d06
-- title:
--   Kuenneth One: is Affine Open inf of is Separated
-- statement:
--   The Kuenneth One construction uses the is Affine Open inf of is Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L200-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L200-L204

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KuennethOne

theorem GlobalTheory.KuennethOne.isAffineOpen_inf_of_isSeparated {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S)
    [IsSeparated f] (U U' : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') :
    IsAffineOpen (U ⊓ U') := by sorry
