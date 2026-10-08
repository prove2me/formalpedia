-- Prove2me | Theorems.Thm_OffloadGNEP_Mono_eq_21
-- name    : OffloadGNEP.Mono.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:35.845654+00:00
-- url     : https://prove2.me/theorems/67d0f137-ecaa-4957-8113-ba845ceab5ac
-- title:
--   (21), p. 13 — the characteristic polynomial of v eᵀ + e vᵀ is η^{N−2}(η² − 2(eᵀv)η + (eᵀv)² − N‖v‖²)
-- statement:
--   Let $N\ge2$, let $v\in\mathbb R^N$, let $e\in\mathbb R^N$ be the all-ones vector and $\|v\|=(\sum_uv_u^2)^{1/2}$ the Euclidean norm. Then the characteristic polynomial of the symmetric matrix $ve^\top+ev^\top$ is
--   $$\eta^{N-2}\Big(\eta^2-2(e^\top v)\,\eta+(e^\top v)^2-N\|v\|^2\Big).$$
--
--   The paper applies this with $v=x^\delta_{clet}$: the matrix has $N-2$ zero eigenvalues and the two eigenvalues $e^\top v\pm\sqrt N\|v\|$, which locates the minimum eigenvalue needed in (22).
--
--   **Formalization Note** The statement is posed for an arbitrary vector $v$, as the cited fact (Bernstein, *Matrix Mathematics*, Fact 4.9.16) is a general one; the paper uses it at $v=x^\delta_{clet}$. The hypothesis $N\ge2$ is added so that the factor $\eta^{N-2}$ is a genuine polynomial (in Lean $N-2$ is truncated subtraction on naturals); for $N=1$ the matrix is the scalar $2v_1$ and the case is not needed. The characteristic polynomial is Mathlib's `Matrix.charpoly`, i.e. $\det(\eta I-M)$.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 13, (21) (citing [6, Fact 4.9.16])

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

namespace OffloadGNEP.Mono

open Polynomial in
theorem eq_21 {N : ℕ} (hN : 2 ≤ N) (v : Fin N → ℝ) :
    (Matrix.vecMulVec v ones + Matrix.vecMulVec ones v).charpoly =
      X ^ (N - 2) * (X ^ 2 - C (2 * ∑ u, v u) * X +
        C ((∑ u, v u) ^ 2 - (N : ℝ) * eucNorm v ^ 2)) := by sorry

end OffloadGNEP.Mono
