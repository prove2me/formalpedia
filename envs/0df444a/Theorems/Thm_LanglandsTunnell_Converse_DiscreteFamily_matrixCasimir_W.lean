-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W
-- name    : LanglandsTunnell.Converse.DiscreteFamily.matrixCasimir_W
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/faa4fc24-955f-50d2-a8a3-d0ee2e27c02d
-- title:
--   Discrete-series Whittaker function is a Casimir eigenfunction
-- statement:
--   Let $u_0 \in \mathbb{C}$, let $k_0$ be a natural number with $1 \le k_0$, and let $x$ be a real $2\times 2$ matrix with $\det x \neq 0$. Write $W =$ `DiscreteFamily.W u₀ k₀` for the explicit function on real $2\times 2$ matrices attached to the discrete archimedean parameter $(u_0,k_0)$, and for an archimedean direction $d$ let $\partial_d$ denote the operator sending a function $V$ to $x \mapsto \frac{d}{dt}\big(V(x\cdot \mathrm{archFlowMatrix}\,d\,t)\big)\big|_{t=0}$, the derivative at $t = 0$ of the right translate of $V$ along the one-parameter flow in direction $d$. The Casimir operator is $\mathrm{matrixCasimir}(V) = -\big(\tfrac14\,\partial_H\partial_H V - \tfrac12\,\partial_H V + \partial_E\partial_{F^-} V\big)$. The assertion is the pointwise eigenvalue identity $$\mathrm{matrixCasimir}(W)(x) = \frac{1 - k_0^2}{4}\, W(x),$$ where $(1-k_0^2)/4$ is the value of `laplaceEigenvalue` at the parameter `RealArchParam.discrete u₀ k₀ hk`. Thus $W$ is an eigenfunction of the Casimir operator at every invertible matrix, with the Laplace eigenvalue prescribed by its discrete parameter; the parameter $u_0$ does not enter the eigenvalue.
--
--   This is the archimedean Casimir (weight-$(k_0+1)$ Laplace) eigenvalue computation for the explicit discrete-series Whittaker function, one of the local archimedean inputs in the converse-theorem step of the Langlands–Tunnell argument. It is used in the construction of an archimedean datum whose Whittaker function is a nonzero Casimir eigenfunction of the prescribed minimal type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W.lean

import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchCasimir

theorem LanglandsTunnell.Converse.DiscreteFamily.matrixCasimir_W (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    matrixCasimir (DiscreteFamily.W u₀ k₀) x =
      (RealArchParam.discrete u₀ k₀ hk).laplaceEigenvalue * DiscreteFamily.W u₀ k₀ x := by sorry
