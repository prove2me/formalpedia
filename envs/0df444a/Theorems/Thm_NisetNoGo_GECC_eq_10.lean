-- Prove2me | Theorems.Thm_NisetNoGo_GECC_eq_10
-- name    : NisetNoGo.GECC.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:22.698824+00:00
-- url     : https://prove2.me/theorems/f91b940b-edc8-4fee-bf3c-fafe5f93952c
-- title:
--   (10) — asymptotic symplectic eigenvalue for negative determinant normal form
-- statement:
--   Suppose the completely positive channel has $M=\eta\Lambda$, where $\eta\ne0$, $\Lambda$ is a real diagonal matrix with $\det\Lambda=-1$ (so $\det M=-\eta^2<0$), and the noise matrix is $N$. For $\eta^2\ne1$, let $\nu_-(r)$ be the smallest partially transposed symplectic eigenvalue after the channel acts on one half of a two-mode squeezed vacuum. Then
--
--   $$2\nu_-(r)^2\longrightarrow\frac{2\det N}{(1+\det M)^2}\qquad(r\to\infty).$$
--
--   This gives the negative determinant calculation of Lemma 2.
--
--   **Formalization Note** The condition $\eta^2\ne1$ is explicit because the right-hand quotient has zero denominator at that boundary. The paper treats the boundary through entanglement breaking.
-- source:
--   Niset, Fiurášek, Cerf, A No-Go Theorem for Gaussian Quantum Error Correction, arXiv:0811.3128v1, p. 3, (10)

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

open QAlgorithms.Papers.Independent.Frontier30.P13
open Filter

namespace NisetNoGo.GECC

theorem eq_10 (η : ℝ) (d : ModeQuadrature (Fin 1) → ℝ)
    (N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (hη : η ≠ 0) (hΛ : (Matrix.diagonal d).det = -1) (hη1 : η ^ 2 ≠ 1)
    (hT : IsCPChannel (η • Matrix.diagonal d) N) :
    Tendsto (fun r : ℝ => 2 * lambdaMin (gammaOut (η • Matrix.diagonal d) N r) ^ 2)
      atTop (nhds (2 * N.det / (1 + (η • Matrix.diagonal d).det) ^ 2)) := by sorry

end NisetNoGo.GECC
