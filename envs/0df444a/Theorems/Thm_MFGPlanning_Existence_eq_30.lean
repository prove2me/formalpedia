-- Prove2me | Theorems.Thm_MFGPlanning_Existence_eq_30
-- name    : MFGPlanning.Existence.eq_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:01:38.797866+00:00
-- url     : https://prove2.me/theorems/f93fb502-31a9-4336-bdcb-4bff81d7cbed
-- title:
--   (30) — $\Sigma^*(-M,-Z)$ is the indicator of the constraint of the control problem (26)
-- statement:
--   Assume $m_0, m_T \in \mathcal K$. For every $(M,Z)$, with $M^n$, $Z^n$ indexed by $n = 0,\dots,N_T-1$,
--   $$\Sigma^*(-M,-Z) = \begin{cases} 0 & \text{if } (M,Z) \text{ satisfies the constraint of (26)},\\ +\infty & \text{otherwise},\end{cases}$$
--   where the constraint of (26) is: with $M^{N_T} := m_T$,
--   $$\frac{M^{n+1}_{i,j}-M^n_{i,j}}{\Delta t} + \nu(\Delta_hM^n)_{i,j} + \mathrm{div}_h(Z^n)_{i,j} = 0 \quad (0\le n<N_T),\qquad M^0 = m_0.$$
--   Hence the optimal control problem (26), minimize $\Theta^*(M,Z)$ subject to the constraint, is equivalent to the unconstrained problem
--   $$\min_{M,Z}\ \Theta^*(M,Z) + \Sigma^*(-M,-Z). \tag{30}$$
--
--   **Formalization Note** The constraint is the definition `PlanningConstraint` of the mission. The hypothesis $m_0, m_T\in\mathcal K$ is the standing assumption of p. 7 ("The data $(m_0)_{i,j}, (m_T)_{i,j}\in\mathcal K$ are discrete probability densities"); equal masses of $m_0$ and $m_T$ are what force $M^0 = m_0$ rather than $M^0 = m_0 + $ const.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.1, p. 9, (30), and p. 7, (26)

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid
import Definitions.Def_MFGPlanning_Existence_Duality

namespace MFGPlanning.Existence

/-- Display (30) of Achdou, Camilli, Capuzzo-Dolcetta, hal-00465404v1 (2010), §3.1, p. 9 (PDF 10):
the control problem (26) is equivalent to the unconstrained problem `min_{M,Z} Θ^*(M, Z) + Σ^*(−M, −Z)`,
because `Σ^*(−M, −Z)` is the indicator (`0` or `+∞`) of the constraint of (26).

Formalization Note: `PlanningConstraint d M Z` is the constraint of (26) with `M^{N_T} = m_T`
appended (`Fin.snoc`) and `M^0 = m_0`. The hypotheses `m_0, m_T ∈ 𝒦` are those of p. 7 ("The data
`(m_0)_{i,j}, (m_T)_{i,j} ∈ 𝒦` are discrete probability densities"). -/
theorem eq_30 (d : Data) (hm0 : InK d d.m0) (hmT : InK d d.mT) :
    ∀ (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ),
      (PlanningConstraint d M Z → SigmaStar d (-M) (-Z) = 0) ∧
        (¬ PlanningConstraint d M Z → SigmaStar d (-M) (-Z) = ⊤) := by sorry

end MFGPlanning.Existence
