-- Prove2me | Theorems.Thm_MatrixSpencer_lemma_C_1
-- name    : MatrixSpencer.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:14.714899+00:00
-- url     : https://prove2.me/theorems/2d37c0ee-5f91-4ce7-b96b-023aee9697df
-- title:
--   Lemma C.1, p.27 — Hessian of a spectral trace function
-- statement:
--   Let $I\subseteq\mathbb R$ be an open interval, $f\in C^2(I)$, and $B=U\mathrm{diag}(\lambda_1,\dots,\lambda_d)U^\top$ with $U$ orthogonal and all $\lambda_a\in I$. Then for every symmetric $Y\in\mathbb R^{d\times d}$,
--
--   $$D^2\mathrm{Tr}f(B)[Y,Y]=\sum_{a,b=1}^df'^{[1]}(\lambda_a,\lambda_b)\,|(U^\top YU)_{ab}|^2,$$
--
--   where $f'^{[1]}$ is the divided difference of $f'$. Here $D^2\mathrm{Tr}f(B)[Y,Y]$ is the second derivative at $t=0$ of $t\mapsto\mathrm{Tr}f(B+tY)$.
--
--   This turns the scalar bounds on divided differences into bounds on the Hessian of $V$.
--
--   Differences from the source:
--   - reading: D² Tr f(B)[Y, Y] → the second derivative at t = 0 of φ(t) = Tr f(B + tY), by HasDerivAt twice; reason: this is the value of the second differential at (Y, Y), which is all (C.3) asserts; no junk deriv is read
--   - encoding: "B symmetric with its spectrum contained in I" → B = U diag(λ) Uᵀ with U orthogonal and λₐ ∈ I; reason: this form implies B is symmetric, and λ is its spectrum
--   - encoding: "open interval" → an open order-connected set; reason: covers bounded intervals, rays and ℝ
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma C.1, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_MatrixSpencer_specTrace
import Definitions.Def_MatrixSpencer_divDiff
open Matrix
open Filter Topology

namespace MatrixSpencer

/-- **Lemma C.1 (Hessian of a spectral trace function).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma C.1, p.27 (PDF p.29): "Let I ⊆ ℝ be an open interval, let f ∈ C²(I), and let B ∈ ℝ^{d×d} be symmetric
matrix with its spectrum contained in the interval I. Write B = U diag(λ₁, …, λ_d)U^⊤ for the spectral
decomposition of B. Then, for every symmetric matrix Y ∈ ℝ^{d×d}, D² Tr f(B)[Y, Y] = Σ^d_{a,b=1}
f′^[1](λₐ, λᵦ)|(U^⊤Y U)ₐᵦ|², (C.3)".

**Formalization Note.** "Open interval" is an open order-connected set. `D²Tr f(B)[Y, Y]` is the second
derivative at `t = 0` of `φ(t) = Tr f(B + tY)`, and it is stated by `HasDerivAt` twice: `φ` has a derivative
`φ′` near `0`, and `φ′` has the printed value as its derivative at `0`. `B` is symmetric because
`B = U diag(λ) U^⊤` with `U` orthogonal; the spectrum condition is `λₐ ∈ I`. -/
theorem lemma_C_1 {d : ℕ} (I : Set ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (B U : Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hB : B = U * Matrix.diagonal lam * Uᵀ) (hlam : ∀ a, lam a ∈ I)
    (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.IsSymm) :
    ∃ φ' : ℝ → ℝ,
      (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun s => specTrace f (B + s • Y)) (φ' t) t) ∧
      HasDerivAt φ'
        (∑ a, ∑ b, divDiff f (lam a) (lam b) * ((Uᵀ * Y * U) a b) ^ 2) 0 := by sorry

end MatrixSpencer
