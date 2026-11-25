-- Prove2me | Theorems.Thm_GlobalTheory_card_finite_subgroup_GL_int_dvd
-- name    : GlobalTheory.card_finite_subgroup_GL_int_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:08:31.811587+00:00
-- url     : https://prove2.me/theorems/1b4de662-3d5e-43d7-aeb3-8842fba74074
-- title:
--   Global Theory: card finite subgroup GL int dvd
-- statement:
--   The Global Theory construction uses the card finite subgroup GL int dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L383-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L383-L409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardFiniteSubgroupGLIntDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.card_finite_subgroup_GL_int_dvd :
    ∀ (n : ℕ) (G : Subgroup (GL (Fin n) ℤ)), Finite G → Nat.card G ∣ 8 ^ n * (2 * n).factorial := by sorry
