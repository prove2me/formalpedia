-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_block_descent
-- name    : NesterovRCD.Sublinear.block_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:31.809468+00:00
-- url     : https://prove2.me/theorems/a130f978-18b3-4424-a05a-120f38a5e297
-- title:
--   (2.3) — $f(x+U_ih_i)\le f(x)+\langle f'_i(x),h_i\rangle+\frac{L_i}2\|h_i\|_{(i)}^2$
-- statement:
--   Let $f:\mathbb R^N\to\mathbb R$ have coordinate-wise Lipschitz continuous gradient with constants $L_1,\dots,L_n>0$ in the sense of (2.2). Then for every $x\in\mathbb R^N$, every block $i$ and every $h_i\in\mathbb R^{n_i}$,
--   $$f(x+U_ih_i)\le f(x)+\langle f'_i(x),h_i\rangle+\frac{L_i}{2}\|h_i\|_{(i)}^2 .$$
--
--   This block version of the descent lemma is the basic estimate behind every coordinate step of the paper.
--
--   **Formalization Note** Blocks are indexed by `Fin n`, $U_ih_i$ is `Pi.single i h`, and $\langle f'_i(x),h_i\rangle$ is the partial gradient functional applied to $h_i$. Convexity is not assumed; the paper does not need it here.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 5, (2.3)

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic

namespace NesterovRCD.Sublinear

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem block_descent (f : Blocks E → ℝ) (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (x : Blocks E) (i : Fin n) (h : E i) :
    f (x + Pi.single i h) ≤ f x + partialGrad f x i h + L i / 2 * ‖h‖ ^ 2 := by sorry

end NesterovRCD.Sublinear
