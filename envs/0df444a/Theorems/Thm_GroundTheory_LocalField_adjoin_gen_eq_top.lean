-- Prove2me | Theorems.Thm_GroundTheory_LocalField_adjoin_gen_eq_top
-- name    : GroundTheory.LocalField.adjoin_gen_eq_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:42.930073+00:00
-- url     : https://prove2.me/theorems/073d3147-8b51-4fb0-b22f-3da3765162f6
-- title:
--   Local Field: adjoin gen eq top
-- statement:
--   The Local Field construction uses the adjoin gen eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L38-L41

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
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.adjoin_gen_eq_top (α : Ksep) : K⟮AdjoinSimple.gen K α⟯ = ⊤ := by sorry
