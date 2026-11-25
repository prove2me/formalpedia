-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_isCyclic
-- name    : GroundTheory.LocalField.IsUnramifiedSubextension.isCyclic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:12.806886+00:00
-- url     : https://prove2.me/theorems/52b00320-5ed0-46cf-83fb-57ec844b950c
-- title:
--   Is Unramified Subextension: is Cyclic
-- statement:
--   The Is Unramified Subextension construction uses the is Cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L81-L88

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]

theorem GroundTheory.LocalField.IsUnramifiedSubextension.isCyclic {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsCyclic (E ≃ₐ[K] E) := by sorry
