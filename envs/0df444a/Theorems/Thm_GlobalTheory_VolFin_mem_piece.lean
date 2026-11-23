-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_mem_piece
-- name    : GlobalTheory.VolFin.mem_piece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:29.731106+00:00
-- url     : https://prove2.me/theorems/11d3edc5-ec95-4418-93b7-b6d73271807d
-- title:
--   Vol Fin: mem piece
-- statement:
--   The Vol Fin construction uses the mem piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L17-L18

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

theorem GlobalTheory.VolFin.mem_piece {R : ι → Subalgebra K F} {γ : ι → F} {e : ℕ} {f : F} :
    f ∈ piece R γ e ↔ ∀ i, f * γ i ^ e ∈ R i := by sorry
