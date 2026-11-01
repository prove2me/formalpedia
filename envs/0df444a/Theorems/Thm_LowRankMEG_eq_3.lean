-- Prove2me | Theorems.Thm_LowRankMEG_eq_3
-- name    : LowRankMEG.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:19.133989+00:00
-- url     : https://prove2.me/theorems/9271b10a-9287-49d0-a903-79fc84a7ec9a
-- title:
--   (3) — $B(X,Y)\ge\frac12\|X-Y\|_*^2$
-- statement:
--   For $X,Y\in\mathcal S_n$ with $Y\succ0$,
--   $$
--   B(X,Y)\ge\frac12\|X-Y\|_*^2.
--   $$
--   This is the $1$-strong convexity of the von Neumann entropy with respect to the nuclear norm, also known as the quantum Pinsker inequality. It turns Bregman bounds into nuclear-norm bounds throughout the analysis.
--
--   Differences from the source:
--   - encoding: X, Y ∈ 𝒮_n → Y also positive definite; reason: log(Y) is undefined on the page at a singular Y; excludes an undefined case only
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eq. (3), p.5

import Mathlib
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_bregman
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

namespace LowRankMEG

/-- **Eq. (3)**: `B(X, Y) ≥ (1/2)‖X − Y‖²_*` for `X, Y ∈ 𝒮_n`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eq. (3), p.5.

**Formalization Note.** `Y ≻ 0`, because `log(Y)` is undefined on the page for singular `Y`. `X` may be
singular (the convention `0 log(0) := 0`). -/
theorem eq_3 {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ PSDPolyApprox.densityMatrices n) (hY : Y ∈ PSDPolyApprox.densityMatrices n) (hYpd : Y.PosDef) :
    1 / 2 * WainwrightHDS.NucNorm.nucNorm (X - Y) ^ 2 ≤ bregman X Y := by sorry

end LowRankMEG
