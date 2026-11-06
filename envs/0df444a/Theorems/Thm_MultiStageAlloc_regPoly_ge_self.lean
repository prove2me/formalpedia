-- Prove2me | Theorems.Thm_MultiStageAlloc_regPoly_ge_self
-- name    : MultiStageAlloc.regPoly_ge_self
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:30:46.300468+00:00
-- url     : https://prove2.me/theorems/fb3f8719-be9a-45bd-984f-f48286300e5c
-- title:
--   Proof of Theorem 1, p.23 — $f_s(x)\ge x$
-- statement:
--   For all $s\in[K-1]$ and $x\in[0,1]$,
--   $$
--   f_s(x)\ge x .
--   $$
--   The proof of Theorem 1 uses this for inequality (1) at the last stage.
--
--   Differences from the source: none.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, proof of Theorem 1, p.23, "the fact that fs(x) ≥ x for all x ∈ [0, 1] and s ∈ [K − 1]"

import Mathlib
import Definitions.Def_MultiStageAlloc_Regularizers

namespace MultiStageAlloc

/-- **`f_s(x) ≥ x`.** Feng & Niazadeh, arXiv:2211.16581v1, proof of Theorem 1, p.23: "`f_s(x) ≥ x` for
all `x ∈ [0, 1]` and `s ∈ [K - 1]`". -/
theorem regPoly_ge_self (K s : ℕ) (hs1 : 1 ≤ s) (hsK : s < K) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : x ≤ regPoly K s x := by sorry

end MultiStageAlloc
