-- Prove2me | Theorems.Thm_GroundTheory_LocalField_minpoly_isEisensteinAt_of_irreducible
-- name    : GroundTheory.LocalField.minpoly_isEisensteinAt_of_irreducible
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:13.376496+00:00
-- url     : https://prove2.me/theorems/4b63e4a2-63c6-4ec6-afa0-9160341aeb50
-- title:
--   Local Field: minpoly is Eisenstein At of irreducible
-- statement:
--   The Local Field construction uses the minpoly is Eisenstein At of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L397-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L397-L499

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
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ

theorem GroundTheory.LocalField.minpoly_isEisensteinAt_of_irreducible :
    (minpoly 𝒪[K] (ϖ : L)).IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) ∧
      (minpoly 𝒪[K] (ϖ : L)).natDegree = Module.finrank K L := by sorry
