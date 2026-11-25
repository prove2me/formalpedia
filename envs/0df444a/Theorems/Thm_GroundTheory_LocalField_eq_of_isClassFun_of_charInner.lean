-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_of_isClassFun_of_charInner
-- name    : GroundTheory.LocalField.eq_of_isClassFun_of_charInner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:12.914022+00:00
-- url     : https://prove2.me/theorems/34f59d3d-1050-420b-8666-fc89a704a694
-- title:
--   Local Field: eq of is Class Fun of char Inner
-- statement:
--   The Local Field construction uses the eq of is Class Fun of char Inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L433-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L433-L436

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
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
open Module Representation
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.eq_of_isClassFun_of_charInner {f f' : G → ℂ} (hf : IsClassFun f) (hf' : IsClassFun f')
    (h : ∀ ψ ∈ irrChars G, charInner G f ψ = charInner G f' ψ) : f = f' := by sorry
