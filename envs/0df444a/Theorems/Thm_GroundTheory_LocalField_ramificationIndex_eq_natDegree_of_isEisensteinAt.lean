-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ramificationIndex_eq_natDegree_of_isEisensteinAt
-- name    : GroundTheory.LocalField.ramificationIndex_eq_natDegree_of_isEisensteinAt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:37.703737+00:00
-- url     : https://prove2.me/theorems/c090aaf7-fc58-567c-8a28-d51f88c232cf
-- title:
--   Local Field: ramification Index eq nat Degree of is Eisenstein At
-- statement:
--   The Local Field construction uses the ramification Index eq nat Degree of is Eisenstein At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L345-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L345-L347

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
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]}
variable (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)
include hf hn hα
variable (hgen : K⟮α⟯ = ⊤)
include hgen

theorem GroundTheory.LocalField.ramificationIndex_eq_natDegree_of_isEisensteinAt : ramificationIndex K L = f.natDegree := by sorry
