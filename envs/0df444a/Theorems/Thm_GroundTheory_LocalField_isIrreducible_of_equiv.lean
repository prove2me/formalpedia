-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isIrreducible_of_equiv
-- name    : GroundTheory.LocalField.isIrreducible_of_equiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:42.590665+00:00
-- url     : https://prove2.me/theorems/81d8a6b3-c807-4450-954c-985ae5a16a24
-- title:
--   Local Field: is Irreducible of equiv
-- statement:
--   The Local Field construction uses the is Irreducible of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L61-L63

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
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GroundTheory.LocalField.isIrreducible_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : Representation.Equiv ρ σ) [ρ.IsIrreducible] : σ.IsIrreducible := by sorry
