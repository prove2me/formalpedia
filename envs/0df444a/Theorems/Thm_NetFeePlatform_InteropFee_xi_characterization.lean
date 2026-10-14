-- Prove2me | Theorems.Thm_NetFeePlatform_InteropFee_xi_characterization
-- name    : NetFeePlatform.InteropFee.xi_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:25.371711+00:00
-- url     : https://prove2.me/theorems/86acf582-f3ae-4593-935e-87cb2fd91fa8
-- title:
--   Proof of Proposition 7, p. 52 — symmetric equilibria satisfy ξ(t; λ) = 0, and for γ ≤ 27/8 every zero of ξ is a symmetric equilibrium
-- statement:
--   Let $J \ge 2$, $w \ge 0$ and $\lambda \in [0,1]$, and let
--   $$\xi(\tau;\lambda) = -\tau + c + \frac{1}{1-n(\tau)} - 2\gamma n(\tau) - \gamma\lambda\big(J-1-\varphi(\tau)\big)n(\tau),$$
--   where $n(\tau)$ and $\varphi(\tau)$ are the common share and diversion ratio when all platforms charge $\tau$. Then:
--
--   1. if the constant profile $\tau$ is a pure-strategy Nash equilibrium in net fees, then $\xi(\tau;\lambda) = 0$;
--   2. if moreover $\gamma \le 27/8$, then conversely every $\tau$ with $\xi(\tau;\lambda) = 0$ makes the constant profile $\tau$ a Nash equilibrium.
--
--   The paper states: "Any solution to $\xi(t;\lambda) = 0$ is a symmetric equilibrium, and conversely any symmetric equilibrium would satisfy $\xi = 0$." This reduces Proposition 7(b) to the zeros of a function of one real variable.
--
--   **Formalization Note** Logit demand, one side. The hypothesis $\gamma \le 27/8$ in part 2 is added: the paper proves first-order sufficiency only under the bound (36) (Proposition 2′'s 3.375), and it is the hypothesis of the mission's goal.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 52, Appendix E.2, proof of Proposition 7 (definition of ξ(t; λ))

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropFee_Symmetric

namespace NetFeePlatform.InteropFee
theorem xi_characterization {J : ℕ} (hJ : 2 ≤ J) (w c γ lam τ : ℝ) (hw : 0 ≤ w)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (NetFeePlatform.Competition.IsEquilibrium w c γ lam (fun _ : Fin J => τ) → xi w c γ lam J τ = 0) ∧
      (γ ≤ 27 / 8 → xi w c γ lam J τ = 0 → NetFeePlatform.Competition.IsEquilibrium w c γ lam (fun _ : Fin J => τ)) := by sorry
end NetFeePlatform.InteropFee
