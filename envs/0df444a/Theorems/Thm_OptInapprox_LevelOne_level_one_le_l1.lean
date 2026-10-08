-- Prove2me | Theorems.Thm_OptInapprox_LevelOne_level_one_le_l1
-- name    : OptInapprox.LevelOne.level_one_le_l1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:27.229784+00:00
-- url     : https://prove2.me/theorems/be639a06-3058-4e30-a2ac-c2040f619baf
-- title:
--   Proof of Theorem 6, p. 25 — Σ_{|S|=1} f̂(S)² = ‖ℓ‖₂² = ⟨f, ℓ⟩ ≤ ‖f‖_∞‖ℓ‖₁ ≤ ‖ℓ‖₁
-- statement:
--   Let $f:\{-1,1\}^n\to[-1,1]$ and let $\ell(x)=\sum_{i=1}^n\hat f(\{i\})x_i$ be its linear part. Then
--   $$\sum_{|S|=1}\hat f(S)^2=\|\ell\|_2^2,\qquad \|\ell\|_2^2=\langle f,\ell\rangle,\qquad \langle f,\ell\rangle\le\|f\|_\infty\|\ell\|_1,\qquad \|f\|_\infty\|\ell\|_1\le\|\ell\|_1 .$$
--
--   Here $\langle f,\ell\rangle=\mathbf E[f\ell]$, $\|\ell\|_1=\mathbf E|\ell|$, $\|\ell\|_2=\sqrt{\mathbf E[\ell^2]}$ and $\|f\|_\infty=\max_x|f(x)|$, all under the uniform measure on the cube.
--
--   This chain is the first step of the proof of Theorem 6: it reduces the level-one weight of a bounded function to the $L^1$ norm of its linear part, a weighted sum of independent random signs.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 25, §10.2, Proof of Theorem 6 (first display)

import Mathlib
import Definitions.Def_OptInapprox_LevelOne_Cube

namespace OptInapprox.LevelOne

theorem level_one_le_l1 {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    levelOneWeight f = l2Norm (linPart f) ^ 2 ∧
    l2Norm (linPart f) ^ 2 = OptInapprox.MaxCut.cubeE (fun x => f x * linPart f x) ∧
    OptInapprox.MaxCut.cubeE (fun x => f x * linPart f x) ≤ supNorm f * l1Norm (linPart f) ∧
    supNorm f * l1Norm (linPart f) ≤ l1Norm (linPart f) := by sorry

end OptInapprox.LevelOne
