-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_matOfUpper_posSemidef
-- name    : ModernConvex.Relaxations.matOfUpper_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:48:20.875992+00:00
-- url     : https://prove2.me/theorems/4a09e328-afaf-4b4d-8420-fc3ffb2b6834
-- title:
--   The upper-triangular Max-Cut SDP body is full dimensional at the origin
-- statement:
--   **The upper-triangular body is full dimensional.**
--
--   In the free coordinates of `ModernConvex_Upper` — where the matrix is determined by its strict upper triangle — the quadratic form is
--   $$v^{\mathsf T}(\texttt{matOfUpper}\,z)v=\sum_i v_i^2+\sum_{i\ne j} z_{ij}v_iv_j ,$$
--   so if every $|z_{ij}|\le B$ then
--   $$v^{\mathsf T}(\texttt{matOfUpper}\,z)v\;\ge\;\sum_i v_i^2-B\Big(\sum_i|v_i|\Big)^2\;\ge\;(1-Bn)\sum_i v_i^2 ,$$
--   using Cauchy–Schwarz $(\sum_i|v_i|)^2\le n\sum_i v_i^2$. Hence $Bn\le1$ implies $\texttt{matOfUpper}\,z\succeq0$.
--
--   In particular $z=0$ is an interior point of $\{z : \texttt{matOfUpper}\,z\succeq0\}$ (take $B=1/n$), so the body is full dimensional — the hypothesis of Bubeck's ellipsoid Theorem 2.4 that the naive coordinates $X\succeq0$, $X_{ii}=1$ fail to satisfy. The bound is deliberately crude: only nonemptiness of the interior and an explicit radius are needed.
-- source:
--   Cauchy-Schwarz bound on the quadratic form; the interior/nonempty-interior hypothesis of Bubeck, arXiv:1405.4980v2, Thm 2.4, p. 250, for the MAXCUT body in upper-triangular coordinates.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_Upper

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **The upper-triangular body is full dimensional at the origin.** If every coordinate of `z`
has modulus at most `B` and `B * n ≤ 1`, then `matOfUpper z` is positive semidefinite; in
particular `0` is an interior point of `{z | matOfUpper z ⪰ 0}`. -/
theorem matOfUpper_posSemidef {n : ℕ} {z : UpIdx n → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hz : ∀ p, |z p| ≤ B) (hBn : B * n ≤ 1) :
    (matOfUpper z).PosSemidef := by sorry

end ModernConvex.Relaxations
