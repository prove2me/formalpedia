-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_sum_irrChars_of_isClassFun
-- name    : GroundTheory.LocalField.eq_sum_irrChars_of_isClassFun
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:38.116816+00:00
-- url     : https://prove2.me/theorems/73b3b9c5-d70c-4d5a-a75d-fdf264b0639e
-- title:
--   Local Field: eq sum irr Chars of is Class Fun
-- statement:
--   The Local Field construction uses the eq sum irr Chars of is Class Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L403-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L403-L426

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

theorem GroundTheory.LocalField.eq_sum_irrChars_of_isClassFun {f : G → ℂ} (hf : IsClassFun f) :
    f = ∑ ψ ∈ irrChars G, charInner G f ψ • ψ := by sorry
