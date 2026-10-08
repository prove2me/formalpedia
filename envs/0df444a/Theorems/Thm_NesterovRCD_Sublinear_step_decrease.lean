-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_step_decrease
-- name    : NesterovRCD.Sublinear.step_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:52.334694+00:00
-- url     : https://prove2.me/theorems/ca7c0b95-44c4-4780-ae59-8262bb2723d3
-- title:
--   (2.4) — $f(x)-f(T_i(x))\ge\frac1{2L_i}(\|f'_i(x)\|^*_{(i)})^2$
-- statement:
--   Let $f$ satisfy (2.2) with constants $L_i>0$ on finite-dimensional normed blocks $\mathbb R^{n_i}$, and let $T_i(x)=x-\frac1{L_i}U_if'_i(x)^\#$ be the optimal coordinate step, for an arbitrary choice of the vectors $s^\#$ of (1.8). Then for every $x$ and every $i$,
--   $$f(x)-f(T_i(x))\ge\frac1{2L_i}\big(\|f'_i(x)\|^*_{(i)}\big)^2 .$$
--
--   This guaranteed decrease of a single coordinate step is what every convergence estimate of the paper is built on.
--
--   **Formalization Note** The choice of $s^\#$ is any `sharp` satisfying `IsSharpSelection`; the dual norm is the operator norm. Convexity is not assumed.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 5, (2.4)

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic

namespace NesterovRCD.Sublinear

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem step_decrease (f : Blocks E → ℝ) (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp)
    (x : Blocks E) (i : Fin n) :
    1 / (2 * L i) * ‖partialGrad f x i‖ ^ 2 ≤ f x - f (coordStep f L sharp i x) := by sorry

end NesterovRCD.Sublinear
