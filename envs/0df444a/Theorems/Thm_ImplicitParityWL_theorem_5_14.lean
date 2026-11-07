-- Prove2me | Theorems.Thm_ImplicitParityWL_theorem_5_14
-- name    : ImplicitParityWL.theorem_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:05.455182+00:00
-- url     : https://prove2.me/theorems/43a1f53f-e061-4668-9212-e5f7beaae111
-- title:
--   Theorem 5.14 — Duplicator survives while $K_T$ is conflict-free
-- statement:
--   Let $T\ge0$ be an integer. If $K_T$ is conflict-free, then Duplicator has a strategy in the bijective pebble game with $k+1$ pebble pairs on $(G_0,G_1)$ to survive for the first $T$ moves.
--
--   This is the lower-bound half of the graph compiler.
--
--   Differences from the source: none.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 5.14, p.34

import Mathlib
import Definitions.Def_ImplicitParityWL_CompiledGraph

namespace ImplicitParityWL

/-- **Theorem 5.14** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.34): let `T ≥ 0`. If `K_T` is conflict-free, then Duplicator has a strategy in the bijective
pebble game with `k + 1` pebble pairs on `(G₀, G₁)` to survive for the first `T` moves. -/
theorem theorem_5_14 (k ℓ : ℕ) (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) {W E : Type} [Fintype W] [Fintype E]
    (I : ImplicitSystem k ℓ W E) (T : ℕ) (hT : I.toParity.ConflictFree T) :
    Survives (I.graph 0) (I.graph 1) T (GameState.empty : GameState _ _ (k + 1)) := by sorry

end ImplicitParityWL
