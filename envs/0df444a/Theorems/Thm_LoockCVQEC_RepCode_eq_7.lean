-- Prove2me | Theorems.Thm_LoockCVQEC_RepCode_eq_7
-- name    : LoockCVQEC.RepCode.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:07.197513+00:00
-- url     : https://prove2.me/theorems/db02748e-d83b-42ea-a028-816e19ae0d7e
-- title:
--   Eq. (7) — three independent displacement channels expand into eight error patterns
-- statement:
--   Let $W$ be any three-mode Wigner function, $0\le\gamma\le1$ an error probability and $\bar x_2$ the displacement size (the identity holds for all real $\gamma,\bar x_2$). Applying the channel "displace by $\bar x_2$ in $x$ with probability $\gamma$" independently to each of the three modes gives
--   $$\begin{aligned}W'(x,p)={}&(1-\gamma)^3W(x,p)\\&+\gamma(1-\gamma)^2\big[W(x-\bar x_2e_1,p)+W(x-\bar x_2e_2,p)+W(x-\bar x_2e_3,p)\big]\\&+\gamma^2(1-\gamma)\big[W(x-\bar x_2(e_1+e_2),p)+W(x-\bar x_2(e_1+e_3),p)+W(x-\bar x_2(e_2+e_3),p)\big]\\&+\gamma^3W(x-\bar x_2(e_1+e_2+e_3),p).\end{aligned}$$
--
--   The paper states this for the encoded state $W=W_{\mathrm{enc}}$; the expansion holds for every $W$. Each term corresponds to one subset of erring channels, weighted by its probability.
--
--   **Formalization Note** The left-hand side is the composition of the three single-mode channels as defined; the shift vectors are written as `![d, 0, 0]` and so on, Lean index $0$ being the paper's mode 1.
--
--   Differences from the source:
--   - generalization: stated for the encoded state W_enc → stated for every three-mode function W and all real γ, x̄₂; reason: the expansion is algebraic in W; W = W_enc gives the page's Eq. (7)
--   - encoding: modes and channels numbered 1, 2, 3 → Fin 3, Lean index j − 1 for the paper's mode j; reason: Lean convention; same instances
-- source:
--   van Loock, A note on quantum error correction with continuous variables, arXiv:0811.3616v1, p. 2, Eq. (7)

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

namespace LoockCVQEC.RepCode

theorem eq_7 (γ d : ℝ) (W : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) (x p : Fin 3 → ℝ) :
    noisy γ d W x p =
      (1 - γ) ^ 3 * W x p
      + γ * (1 - γ) ^ 2 * W (x - ![d, 0, 0]) p
      + γ * (1 - γ) ^ 2 * W (x - ![0, d, 0]) p
      + γ * (1 - γ) ^ 2 * W (x - ![0, 0, d]) p
      + γ ^ 2 * (1 - γ) * W (x - ![d, d, 0]) p
      + γ ^ 2 * (1 - γ) * W (x - ![d, 0, d]) p
      + γ ^ 2 * (1 - γ) * W (x - ![0, d, d]) p
      + γ ^ 3 * W (x - ![d, d, d]) p := by sorry

end LoockCVQEC.RepCode
