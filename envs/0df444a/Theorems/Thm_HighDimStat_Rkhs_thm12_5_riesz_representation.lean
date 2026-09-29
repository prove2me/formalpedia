-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_thm12_5_riesz_representation
-- name    : HighDimStat.Rkhs.thm12_5_riesz_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:23:28.667837+00:00
-- url     : https://prove2.me/theorems/8432eabe-bdff-48a9-abbe-7dd7ecd2f845
-- title:
--   The Riesz representation theorem for a Hilbert space (Theorem 12.5)
-- statement:
--   **Theorem 12.5 (Riesz representation theorem).** Every bounded linear functional on a
--   Hilbert space is realized, uniquely, as an inner product against a fixed vector — the
--   Hilbert-space fact the whole Moore-Aronszajn correspondence rests on.
--
--   Let $H$ be a (real) Hilbert space and $L:H\to\mathbb R$ a bounded linear functional (there
--   is $M<\infty$ with $|L(f)|\le M\|f\|_H$ for all $f\in H$). Then there exists a unique
--   $g\in H$ such that
--
--   $$
--   L(f) = \langle f,g\rangle_H \qquad \text{for all } f\in H.
--   $$
--
--   The vector $g$ is called the *representer* of $L$. Applied to the evaluation functional
--   $L_x(f):=f(x)$ on a reproducing kernel Hilbert space, this is exactly what identifies
--   $K(\cdot,x)$ as the representer of evaluation at $x$ (Theorem 12.13's proof).
--
--   **Formalization Note** Stated for an arbitrary real Hilbert space `H` (`[CompleteSpace
--   H]`), matching the book's own generality; not specialized to any RKHS. This is a
--   standard Hilbert-space fact already present in Mathlib (`InnerProductSpace.toDual`, a
--   linear isometric equivalence between a Hilbert space and its continuous dual); no
--   platform prior art was found under this or related searches, so it is drafted here as its
--   own mission item rather than cited as `kind: reference`.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 385 (PDF p. 405), Theorem 12.5

import Mathlib

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 12.5 (Riesz representation theorem, p. 385): every bounded linear functional `L`
on a Hilbert space `H` has a unique representer `g ∈ H` with `L(f) = ⟨f, g⟩_H` for all
`f ∈ H`. -/
theorem thm12_5_riesz_representation (L : H →ₗ[ℝ] ℝ)
    (hL : ∃ M : ℝ, ∀ f : H, |L f| ≤ M * ‖f‖) :
    ∃! g : H, ∀ f : H, L f = ⟪f, g⟫ := by sorry

end HighDimStat.Rkhs
