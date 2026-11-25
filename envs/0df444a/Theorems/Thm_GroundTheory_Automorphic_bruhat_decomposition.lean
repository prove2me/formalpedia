-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_bruhat_decomposition
-- name    : GroundTheory.Automorphic.bruhat_decomposition
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:32.146251+00:00
-- url     : https://prove2.me/theorems/adc27240-58e7-589a-80ba-6045863cea82
-- title:
--   Automorphic: bruhat decomposition
-- statement:
--   The Automorphic construction uses the bruhat decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L322-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L322-L325

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]

theorem GroundTheory.Automorphic.bruhat_decomposition (g : GL (Fin n) k) :
    ∃! σ : Equiv.Perm (Fin n), g ∈ doubleCoset (permGL k σ) (borel n k) (borel n k) := by sorry
