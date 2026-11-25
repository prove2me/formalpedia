-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_sub_algebraMap_mem_maximalIdeal
-- name    : GroundTheory.LocalField.exists_sub_algebraMap_mem_maximalIdeal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:14:52.331713+00:00
-- url     : https://prove2.me/theorems/f0a320d7-0c26-4c75-ad4e-5e35924577e8
-- title:
--   Local Field: exists sub algebra Map mem maximal Ideal
-- statement:
--   The Local Field construction uses the exists sub algebra Map mem maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L195-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L195-L202

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
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
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.exists_sub_algebraMap_mem_maximalIdeal (h : residueDegree K L = 1) (w : 𝒪[L]) :
    ∃ c : 𝒪[K], w - algebraMap 𝒪[K] 𝒪[L] c ∈ IsLocalRing.maximalIdeal 𝒪[L] := by sorry
