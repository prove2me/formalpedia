-- Prove2me | Theorems.Thm_ImpulseGames_LinearGame_eq_4_17_unique_zero
-- name    : ImpulseGames.LinearGame.eq_4_17_unique_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:28:08.076981+00:00
-- url     : https://prove2.me/theorems/81fa21cc-07bd-468a-b96e-1a20310bd269
-- title:
--   (4.17): $F(y)=2y+\theta c-\eta\log\frac{\eta+y}{\eta-y}$ has a unique zero $\xi\in(0,\eta)$
-- statement:
--   Under the standing assumptions of Section 4.1 and $c>0$, let $\theta=\sqrt{2\rho/\sigma^2}$, $\eta=(1-\lambda\rho)/\rho>0$ and, for $y\in(0,\eta)$,
--   $$F(y)=2y+\theta c-\eta\log\Big(\frac{\eta+y}{\eta-y}\Big).$$
--   Then there is exactly one $\xi\in(0,\eta)$ with $F(\xi)=0$.
--
--   The zero $\xi$ is the parameter from which the explicit thresholds and payoffs (4.20) of the equilibria are built.
--
--   **Formalization Note.** The hypothesis $c>0$ is added: the paper uses $F(0^+)=\theta c>0$, and with $c=0$ (allowed by $c\ge\tilde c\ge0$, $(c,\lambda)\ne(\tilde c,\tilde\lambda)$) $F$ is negative on $(0,\eta)$ and has no zero.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, proof of Proposition 4.2, (4.17) (p. 16)

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Candidates

namespace ImpulseGames.LinearGame

/-- (4.17), p. 16: under the standing assumptions of Section 4.1 and `c > 0`, the function
`F(y) = 2y + θc − η log((η + y)/(η − y))` has exactly one zero `ξ` in `(0, η)`. -/
theorem eq_4_17_unique_zero (M : Model) (hM : M.Standing) (hc : 0 < M.c) :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo 0 (eta M) ∧ F M ξ = 0 := by sorry

end ImpulseGames.LinearGame
