-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_det_krylov_ne_zero
-- name    : GroundTheory.Automorphic.exists_det_krylov_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:25.314566+00:00
-- url     : https://prove2.me/theorems/82bb6d70-e22e-469e-a807-2d6bc387b326
-- title:
--   Automorphic: exists det krylov ne zero
-- statement:
--   The Automorphic construction uses the exists det krylov ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L85-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L85-L112

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
variable {E : Type*} [Field E]
variable [Infinite E]

theorem GroundTheory.Automorphic.exists_det_krylov_ne_zero {L : Type*} [Field L] (φ : E →+* L)
    (M : Matrix (Fin n) (Fin n) E) (w : Fin n → L) (hw : (krylov (M.map φ) w).det ≠ 0) :
    ∃ v : Fin n → E, (krylov M v).det ≠ 0 := by sorry
