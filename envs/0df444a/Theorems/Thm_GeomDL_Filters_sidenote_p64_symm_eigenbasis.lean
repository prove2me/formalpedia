-- Prove2me | Theorems.Thm_GeomDL_Filters_sidenote_p64_symm_eigenbasis
-- name    : GeomDL.Filters.sidenote_p64_symm_eigenbasis
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:24.996808+00:00
-- url     : https://prove2.me/theorems/479c84f9-f1e7-49f4-b3f0-8c79e4fd0ba8
-- title:
--   Side-note, p. 64 — for undirected W the Laplacian is symmetric and Δ = ΦΛΦᵀ with Φ orthogonal
-- statement:
--   Let $W\in\mathbb R^{n\times n}$ be symmetric, $W=W^\top$ (an undirected weighted graph), and let $\Delta=D-W$ be its Laplacian. Then $\Delta$ is symmetric, and it has orthogonal eigenvectors diagonalising it: there are an orthogonal matrix $\Phi=(\varphi_1,\dots,\varphi_n)$, $\Phi^\top\Phi=I$, and real numbers $\lambda_1,\dots,\lambda_n$ with
--   $$\Delta=\Phi\Lambda\Phi^\top,\qquad \Lambda=\operatorname{diag}(\lambda_1,\dots,\lambda_n).$$
--
--   The columns of $\Phi$ serve as the graph analogue of the Fourier basis, and the $\lambda_i$ are the Laplacian eigenvalues.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning (arXiv:2104.13478v2), §4.6, p. 64, side-note "The fact that the graph is assumed to be undirected is important" and "Spectral analysis on meshes"

import Mathlib
import Definitions.Def_GeomDL_Filters_Defs

namespace GeomDL.Filters
open Matrix
/-- §4.6, p. 64 and its side-note: for an undirected graph (`W` symmetric) the Laplacian is
symmetric and has orthogonal eigenvectors `Φ` diagonalising it, `Δ = ΦΛΦᵀ` with
`Λ = diag(λ₁, …, λₙ)`. -/
theorem sidenote_p64_symm_eigenbasis {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hW : W.IsSymm) :
    (lap W).IsSymm ∧
      ∃ Φ ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∃ lam : Fin n → ℝ,
        lap W = Φ * Matrix.diagonal lam * Φᵀ := by sorry
end GeomDL.Filters
