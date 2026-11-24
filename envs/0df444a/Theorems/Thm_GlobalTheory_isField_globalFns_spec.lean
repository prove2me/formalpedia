-- Prove2me | Theorems.Thm_GlobalTheory_isField_globalFns_spec
-- name    : GlobalTheory.isField_globalFns_spec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:25.325375+00:00
-- url     : https://prove2.me/theorems/6f93a67d-d0f8-40c6-958c-fd4e24f3acd2
-- title:
--   Global Theory: is Field global Fns spec
-- statement:
--   The Global Theory construction uses the is Field global Fns spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsFieldGlobalFnsSpec.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsFieldGlobalFnsSpec.lean#L23-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsFieldGlobalFnsSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.isField_globalFns_spec (K : Type) [Field K] :
    IsField Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) := by sorry
