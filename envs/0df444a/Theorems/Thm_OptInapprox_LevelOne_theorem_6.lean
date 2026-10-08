-- Prove2me | Theorems.Thm_OptInapprox_LevelOne_theorem_6
-- name    : OptInapprox.LevelOne.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:22.858624+00:00
-- url     : https://prove2.me/theorems/69fb9697-56ec-4d39-89a3-a2fa2d50288e
-- title:
--   Theorem 6, p. 12 — if f : {−1,1}ⁿ → [−1,1] has all influences ≤ δ then Σ_{|S|=1} f̂(S)² ≤ 2/π + Cδ, C = 2(1 − √(2/π))
-- statement:
--   Let $f:\{-1,1\}^n\to[-1,1]$ and $\delta\ge 0$, and suppose that every coordinate has small influence: $\mathrm{Inf}_i(f)\le\delta$ for all $i\in[n]$. Then the Fourier weight of $f$ at level 1 satisfies
--   $$\sum_{|S|=1}\hat f(S)^2\le\frac{2}{\pi}+C\delta,\qquad\text{where } C=2\Big(1-\sqrt{2/\pi}\Big).$$
--
--   Here $\hat f(S)=\mathbf E[f\chi_S]$ is the Fourier coefficient of $f$ under the uniform measure on the cube, and $\mathrm{Inf}_i(f)$ is the influence of Definition 2: the average over the other coordinates of the variance of $f$ in $x_i$.
--
--   The constant $2/\pi$ is the squared $L^1$ norm of a standard Gaussian, and majority on many variables shows it cannot be lowered. The theorem is the $\rho\to 0$ special case of the Majority Is Stablest theorem, with an explicit error term linear in the maximal influence.
--
--   **Formalization Note** The hypothesis $\delta\ge0$ is added. Influences are nonnegative, so for $n\ge1$ it follows from the other hypotheses; for $n=0$ the hypothesis on influences is empty and $\delta\ge 0$ is what the page tacitly assumes. The range hypothesis $f(x)\in[-1,1]$ is written $|f(x)|\le 1$. The statement is posed exactly as printed; the published proof's first step ($|\hat f(\{i\})|\le\mathrm{Inf}_i(f)$) is valid for $\{-1,1\}$-valued $f$ but not for $[-1,1]$-valued $f$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 12, §6.2, Theorem 6 (proof: p. 25, §10.2)

import Mathlib
import Definitions.Def_OptInapprox_LevelOne_Cube

namespace OptInapprox.LevelOne

theorem theorem_6 {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : ∀ i : Fin n, influence i f ≤ δ) :
    levelOneWeight f ≤ 2 / Real.pi + 2 * (1 - Real.sqrt (2 / Real.pi)) * δ := by sorry

end OptInapprox.LevelOne
