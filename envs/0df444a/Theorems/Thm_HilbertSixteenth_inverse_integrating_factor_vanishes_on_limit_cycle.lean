-- Prove2me | Theorems.Thm_HilbertSixteenth_inverse_integrating_factor_vanishes_on_limit_cycle
-- name    : HilbertSixteenth.inverse_integrating_factor_vanishes_on_limit_cycle
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:50:44.36853+00:00
-- url     : https://prove2.me/theorems/2cb5c0bf-98e2-4685-8499-47b7029b1003
-- title:
--   Theorem 5 (Giacomini–Llibre–Viano): limit cycles lie in the zero set of an inverse integrating factor
-- statement:
--   Let $X=(P,Q)$ be a $C^1$ vector field on an open set $U\subseteq\mathbb R^2$ and let $V:U\to\mathbb R$ be an inverse integrating factor of $X$, i.e. a $C^1$ function with
--   $$P\frac{\partial V}{\partial x}+Q\frac{\partial V}{\partial y}=\Big(\frac{\partial P}{\partial x}+\frac{\partial Q}{\partial y}\Big)V\quad\text{on } U.$$
--   If $\gamma\subseteq U$ is a limit cycle of $X$, then $\gamma\subseteq\{(x,y)\in U : V(x,y)=0\}$.
--
--   This result is used in the proofs of Theorems 1 and 4.
--
--   **Formalization Note** The vector field is a function on all of $\mathbb R^2$ required to be $C^1$ only on $U$; its values outside $U$ are irrelevant because the limit cycle lies in the open set $U$.
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554, §7, Theorem 5 (H. Giacomini, J. Llibre, M. Viano, Nonlinearity 9 (1996) 501–516).

import Definitions.Def_HilbertSixteenth_Dynamics

namespace HilbertSixteenth
theorem inverse_integrating_factor_vanishes_on_limit_cycle (F : ℝ × ℝ → ℝ × ℝ)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) (V : ℝ × ℝ → ℝ)
    (hV : IsInverseIntegratingFactor F U V) (O : Set (ℝ × ℝ)) (hOU : O ⊆ U)
    (hO : IsLimitCycle F O) : ∀ p ∈ O, V p = 0 := by sorry
end HilbertSixteenth
