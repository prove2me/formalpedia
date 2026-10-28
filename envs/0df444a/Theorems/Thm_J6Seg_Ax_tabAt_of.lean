-- Prove2me | Theorems.Thm_J6Seg_Ax_tabAt_of
-- name    : J6Seg.Ax.tabAt_of
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:53:30.771823+00:00
-- url     : https://prove2.me/theorems/a4e15763-a81f-40a6-b2ba-21706c0c14ab
-- title:
--   Per-axis TabAt from ChunkTabBnd6
-- statement:
--   The global package `ChunkTabBnd6 P` is definitionally the eventual per-axis table bound `TabAt`.
--
--   Unpacking the existential yields a threshold $n_1$ such that every admissible axis carries `TabAt`. This is the bridge from the uniform table lemma to the per-axis hypothesis of `chunk_budget_at`.
-- source:
--   xuanji round-six (Solutions.J6SegAx facts); definitional bridge ChunkTabBnd6 → TabAt; feeds chunkBudget6_all

import Definitions.Def_IntMul_Kappa_R6_Defs70

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg J6Seg.Ax
open IntMul.Kappa.R6

namespace J6Seg.Ax

theorem tabAt_of (P : Prm) (h : ChunkTabBnd6 P) :
    ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → ∀ src : ℕ → ℕ, SrcOK6 P n src →
      ∀ D : ℕ, dP6 P n = D + 1 → ∀ k ≤ D, TabAt P n src k := by
  sorry

end J6Seg.Ax
