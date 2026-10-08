-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_lemma2_upper
-- name    : NesterovRCD.Sublinear.lemma2_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:19.096467+00:00
-- url     : https://prove2.me/theorems/4e7430fd-9819-474b-b88a-38d52e46b5ef
-- title:
--   Lemma 2, (2.10) — $f(x)\le f(y)+\langle\nabla f(y),x-y\rangle+\frac12S_\alpha\|x-y\|^2_{1-\alpha}$
-- statement:
--   Let $f:\mathbb R^N\to\mathbb R$ be convex and satisfy (2.2) with constants $L_i>0$, and let $\alpha\in\mathbb R$. Then for all $x,y\in\mathbb R^N$
--   $$f(x)\le f(y)+\langle\nabla f(y),x-y\rangle+\tfrac12S_\alpha\|x-y\|_{1-\alpha}^2 .$$
--
--   This quadratic upper bound in the weighted norm gives the starting estimate $\varphi_0-f^*\le\frac12S_\alpha R^2_{1-\alpha}(x_0)$ in the proof of Theorem 1, which produces the constant $4$ in $k+4$.
--
--   **Formalization Note** As for (2.9), convexity is the standing assumption of §2 and is stated explicitly. $\langle\nabla f(y),x-y\rangle$ is the Fréchet derivative of $f$ at $y$ applied to $x-y$.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 6, Lemma 2, (2.10)

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic

namespace NesterovRCD.Sublinear

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem lemma2_upper (f : Blocks E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (L : Fin n → ℝ) (hL : CoordLipschitz f L) (α : ℝ) (x y : Blocks E) :
    f x ≤ f y + fderiv ℝ f y (x - y) + S L α / 2 * wnorm L (1 - α) (x - y) ^ 2 := by sorry

end NesterovRCD.Sublinear
