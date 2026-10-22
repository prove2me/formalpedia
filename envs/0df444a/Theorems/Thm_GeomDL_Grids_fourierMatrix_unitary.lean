-- Prove2me | Theorems.Thm_GeomDL_Grids_fourierMatrix_unitary
-- name    : GeomDL.Grids.fourierMatrix_unitary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:26.203657+00:00
-- url     : https://prove2.me/theorems/f8bf7035-d402-4f01-bca4-028dc3f0b91d
-- title:
--   §4.2, side-note p. 38 — the Fourier matrix is unitary, Φ*Φ = I
-- statement:
--   Let $n \ge 1$ and let $\Phi = (\varphi_0, \dots, \varphi_{n-1})$ be the $n \times n$ Fourier matrix with columns $\varphi_k(u) = n^{-1/2} e^{2\pi i k u/n}$. Writing $\Phi^*$ for the conjugate transpose,
--   $$\Phi^* \Phi = I .$$
--
--   So the columns of $\Phi$ are orthonormal for the Hermitian inner product and multiplication by $\Phi^*$ (the DFT) is a change of coordinates whose inverse is multiplication by $\Phi$ (the inverse DFT).
--
--   **Formalization Note** The side-note calls $\Phi$ "an orthogonal matrix"; since $\Phi$ is complex, the property it writes, $\Phi^*\Phi = I$ with $\Phi^*$ the conjugate transpose (the book's own convention, side-note p. 38), is unitarity. The Lean statement uses `conjTranspose`.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.2, side-note p. 38, "Since the Fourier transform is an orthogonal matrix (Φ∗Φ = I)"

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open Matrix

namespace GeomDL.Grids
/-- Bronstein et al. §4.2, side-note p. 38: the Fourier matrix satisfies `Φ*Φ = I`, where `Φ*` is
the conjugate transpose (the side-note calls `Φ` orthogonal; over `ℂ` this is unitarity). -/
theorem fourierMatrix_unitary {n : ℕ} [NeZero n] :
    (fourierMatrix n)ᴴ * fourierMatrix n = 1 := by sorry
end GeomDL.Grids
