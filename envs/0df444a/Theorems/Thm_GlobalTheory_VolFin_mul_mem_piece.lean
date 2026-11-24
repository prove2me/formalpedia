-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_mul_mem_piece
-- name    : GlobalTheory.VolFin.mul_mem_piece
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:08.124702+00:00
-- url     : https://prove2.me/theorems/8419ff0c-4ae5-4a43-b7ee-6a4a57034224
-- title:
--   Vol Fin: mul mem piece
-- statement:
--   The Vol Fin construction uses the mul mem piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L20-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}

theorem GlobalTheory.VolFin.mul_mem_piece {R : ι → Subalgebra K F} {γ : ι → F} {e e' : ℕ} {a b : F}
    (ha : a ∈ piece R γ e) (hb : b ∈ piece R γ e') : a * b ∈ piece R γ (e + e') := by sorry
