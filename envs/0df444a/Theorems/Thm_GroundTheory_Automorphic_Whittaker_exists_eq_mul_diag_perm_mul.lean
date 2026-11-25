-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_eq_mul_diag_perm_mul
-- name    : GroundTheory.Automorphic.Whittaker.exists_eq_mul_diag_perm_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:41:12.169783+00:00
-- url     : https://prove2.me/theorems/2b49c8cf-73ff-4681-b8ef-e112015d2852
-- title:
--   Whittaker: exists eq mul diag perm mul
-- statement:
--   The Whittaker construction uses the exists eq mul diag perm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L573-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L573-L579

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.Whittaker.exists_eq_mul_diag_perm_mul {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)}
    (hg : bruhatCell g = w) :
    ∃ t : Fin n → Fˣ, ∃ a ∈ Iwasawa.unipotent F n, ∃ b ∈ Iwasawa.unipotent F n,
      g = a * (Iwasawa.diagGL F n t * permGL F w) * b := by sorry
