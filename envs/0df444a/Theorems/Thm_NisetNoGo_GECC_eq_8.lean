-- Prove2me | Theorems.Thm_NisetNoGo_GECC_eq_8
-- name    : NisetNoGo.GECC.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:13.016598+00:00
-- url     : https://prove2.me/theorems/89f63486-32db-41d0-9c61-d059da2745c4
-- title:
--   (8) — asymptotic symplectic eigenvalue for positive determinant normal form
-- statement:
--   Suppose the completely positive channel has $M=\eta I$ with $\eta\ne0$ (so $\det M=\eta^2>0$) and noise matrix $N$. Let $\nu_-(r)$ be the smallest symplectic eigenvalue of the partial transpose of the covariance obtained by sending one half of a two-mode squeezed vacuum through this channel. Then, as $r\to\infty$,
--
--   $$2\nu_-(r)^2\longrightarrow\frac{2\det N}{(1+\eta^2)^2}.$$
--
--   This is the positive determinant calculation in Lemma 2. The covariance uses $\cosh(2r)$ and $\sinh(2r)$, as in (6).
-- source:
--   Niset, Fiurášek, Cerf, A No-Go Theorem for Gaussian Quantum Error Correction, arXiv:0811.3128v1, p. 3, (6)–(8)

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

open QAlgorithms.Papers.Independent.Frontier30.P13
open Filter

namespace NisetNoGo.GECC

theorem eq_8 (η : ℝ)
    (N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (hη : η ≠ 0) (hT : IsCPChannel (η • 1) N) :
    Tendsto (fun r : ℝ => 2 * lambdaMin (gammaOut (η • 1) N r) ^ 2)
      atTop (nhds (2 * N.det / (1 + η ^ 2) ^ 2)) := by sorry

end NisetNoGo.GECC
