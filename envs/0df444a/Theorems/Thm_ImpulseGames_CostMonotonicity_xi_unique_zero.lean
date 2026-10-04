-- Prove2me | Theorems.Thm_ImpulseGames_CostMonotonicity_xi_unique_zero
-- name    : ImpulseGames.CostMonotonicity.xi_unique_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:39:26.263197+00:00
-- url     : https://prove2.me/theorems/f945dfa4-dd0d-4e66-8432-2ad3047cedb7
-- title:
--   Proof of Prop. 4.2, (4.17) — for $c>0$, $\xi(c)$ is the unique zero of $F$ in $(0,\eta)$
-- statement:
--   Let the parameters satisfy the standing assumptions of Section 4.1 ($\rho>0$, $\sigma>0$, $s_1<s_2$, $\tilde c\ge0$, $\lambda\ge\tilde\lambda\ge0$, $1-\lambda\rho>0$), let $\theta=\sqrt{2\rho/\sigma^2}$, $\eta=(1-\lambda\rho)/\rho$, and for $y\in(0,\eta)$ let
--   $$F_c(y) = 2y + \theta c - \eta\log\left(\frac{\eta+y}{\eta-y}\right).$$
--   Let $\xi(c) = \sup\{y\in(0,\eta) : F_c(y)\ge 0\}$. Then for every $c>0$:
--
--   1. $\xi(c)\in(0,\eta)$;
--   2. $F_c(\xi(c)) = 0$;
--   3. every $y\in(0,\eta)$ with $F_c(y)=0$ equals $\xi(c)$.
--
--   This is the claim in the proof of Proposition 4.2 that $F$ has a unique zero $\xi\in(0,\eta)$. It certifies that the supremum used to define $\xi(c)$ is the paper's $\xi$, so every later statement about $\xi(c)$, $\Gamma(c)$ and the thresholds (4.20) is about the paper's objects.
--
--   **Formalization Note.** The hypothesis $c>0$ is added: the paper's standing assumptions allow $c=0$ when $\tilde c=0$ and $\lambda>\tilde\lambda$, but then $F(0^+)=0$ and $F$ is strictly decreasing, so $F$ has no zero in $(0,\eta)$. The paper's own argument uses $F(0^+)=\theta c>0$.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, proof of Proposition 4.2, (4.17) (p. 16)

import Mathlib
import Definitions.Def_ImpulseGames_CostMonotonicity_Thresholds

namespace ImpulseGames.CostMonotonicity

theorem xi_unique_zero (P : Params) (hP : P.Standing) (c : ℝ) (hc : 0 < c) :
    P.xi c ∈ Set.Ioo 0 P.eta ∧ P.F c (P.xi c) = 0 ∧
      ∀ y ∈ Set.Ioo 0 P.eta, P.F c y = 0 → y = P.xi c := by sorry

end ImpulseGames.CostMonotonicity
