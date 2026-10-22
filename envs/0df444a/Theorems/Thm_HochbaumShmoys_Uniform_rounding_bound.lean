-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_rounding_bound
-- name    : HochbaumShmoys.Uniform.rounding_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:33.177833+00:00
-- url     : https://prove2.me/theorems/c0afaf25-954d-4f21-88ef-b3e928b58d92
-- title:
--   §3, proof of Lemma 4 — $p_j\le(1+\varepsilon)\bar p_j$ (p. 548)
-- statement:
--   Let $N\ge2$ be an integer and $\delta=1/N$. For a size $x$ with $0<x\le1$, lying in interval $k$, i.e. $x\in(\delta^{k+1},\delta^k]$, let $\bar x=\lfloor x/\delta^{k+2}\rfloor\,\delta^{k+2}$ be its rounded size. Then
--   $$x\le(1+\delta)\,\bar x .$$
--
--   Rounding down loses at most a factor $1+\delta$ on each piece; together with the bound on the rounded content of each bin, this gives the relaxation factor $(1+\delta)^2=1+2\delta+\delta^2$ of all-pack.
--
--   **Formalization Note** The paper writes $\varepsilon$ for the parameter of all-pack; it is $\delta=1/N$ here, with $1/\delta$ a positive integer as the paper assumes in §3, and $N\ge2$ (the paper's $\varepsilon\le1/2$).
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 548, §3, proof of Lemma 4 — p_j ≤ (1 + ε)p̄_j

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Rounding

namespace HochbaumShmoys.Uniform

theorem rounding_bound (N : ℕ) (hN : 2 ≤ N) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x ≤ (1 + (N : ℝ)⁻¹) * roundDown N x := by sorry

end HochbaumShmoys.Uniform
