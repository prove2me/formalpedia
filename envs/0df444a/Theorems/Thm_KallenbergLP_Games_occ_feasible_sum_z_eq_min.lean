-- Prove2me | Theorems.Thm_KallenbergLP_Games_occ_feasible_sum_z_eq_min
-- name    : KallenbergLP.Games.occ_feasible_sum_z_eq_min
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:56:20.410978+00:00
-- url     : https://prove2.me/theorems/83e607ab-ac07-4023-aa3d-cc2bd029bea9
-- title:
--   Theorem 6.2.4 (i) — (x(π), z(π)) is feasible for (6.2.2) and Σ z_i(π) = min over ρ of Σ β_j v_j(π^∞, ρ^∞)
-- statement:
--   Let $(E,A,B,p,r)$ be a stochastic game satisfying Assumptions 6.2.1 and 6.2.2, and let $\beta_j > 0$, $j \in E$. For a stationary policy $\pi^\infty$ of player I put
--   $$x_{ia}(\pi) = [\beta^T(I-P(\pi))^{-1}]_i\,\pi_{ia}, \qquad z_i(\pi) = \min_{b \in B(i)} r_{ib}(\pi)\cdot\sum_a x_{ia}(\pi).$$
--   Then $(x(\pi), z(\pi))$ is a feasible solution of the linear program (6.2.2), and
--   $$\sum_i z_i(\pi) = \min_{\rho}\ \sum_j \beta_j\, v_j(\pi^\infty,\rho^\infty),$$
--   the minimum being taken over the stationary policies $\rho^\infty$ of player II and being attained.
--
--   Together with part (ii), this identifies the feasible solutions of (6.2.2) with the stationary policies of the controlling player.
--
--   **Formalization Note** The book writes the identity with ":=", meaning equality. The minimum is stated as `IsLeast` of the set of values $\sum_j\beta_j v_j(\pi^\infty,\rho^\infty)$ over stationary $\rho^\infty$, which asserts both the lower bound and its attainment.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 198, Theorem 6.2.4 (i) (with x_ia(π), z_i(π) defined on p. 198; Assumptions 6.2.1, 6.2.2 and β_j > 0 standing, pp. 192–194)

import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController

namespace KallenbergLP.Games

/-- Theorem 6.2.4 (i) (p. 198): under Assumptions 6.2.1 and 6.2.2, with `β ≫ 0`, for every
stationary policy `π^∞` of player I, `(x(π), z(π))` is feasible for (6.2.2) and
`∑_i z_i(π) = min_ρ ∑_j β_j v_j(π^∞, ρ^∞)`, the minimum over stationary policies of player II. -/
theorem occ_feasible_sum_z_eq_min {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) (hC : Assumption622 G)
    (β' : Fin N → ℝ) (hβ : ∀ j, 0 < β' j)
    (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) :
    LP622Feasible G β' (occ G β' π) (zval G β' π) ∧
      IsLeast
        {c : ℝ | ∃ (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ),
          c = ∑ j, β' j * totalReward G (stationary1 G π hπ) (stationary2 G ρ hρ) j}
        (∑ i, zval G β' π i) := by sorry

end KallenbergLP.Games
