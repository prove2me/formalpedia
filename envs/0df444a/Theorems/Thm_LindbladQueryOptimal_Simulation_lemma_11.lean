-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_11
-- name    : LindbladQueryOptimal.Simulation.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:43.105203+00:00
-- url     : https://prove2.me/theorems/e46f7794-e011-4342-9818-2884873febf6
-- title:
--   Lemma 11 — Cayley block identity
-- statement:
--   Let $L$ be a system matrix, let $\widetilde L=\left(\begin{smallmatrix}0&L^\dagger\\L&0\end{smallmatrix}\right)$, and write $C(A)=(I-iA)(I+iA)^{-1}$ and $F(A)=(I-A)(I+A)^{-1}$. For every vector $y$,
--   $$C(\widetilde L)(y\oplus0)=F(L^\dagger L)y\oplus\bigl(-2iL(I+L^\dagger L)^{-1}y\bigr).$$
--   The matrix equality asserts this simultaneously for all vectors. It identifies the no-jump and jump blocks without an invertibility assumption on $L$.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 11, p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_11 (n : ℕ) (L : Op (Bits n)) :
    cayley (dilation L) * (inj0 : Matrix (Sum (Bits n) (Bits n)) (Bits n) ℂ) =
      Matrix.fromRows (realCayley (Lᴴ * L))
        ((-2 * Complex.I) • (L * (1 + Lᴴ * L)⁻¹)) := by sorry

end LindbladQueryOptimal.Simulation
