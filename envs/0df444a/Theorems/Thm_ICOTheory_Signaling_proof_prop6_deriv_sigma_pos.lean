-- Prove2me | Theorems.Thm_ICOTheory_Signaling_proof_prop6_deriv_sigma_pos
-- name    : ICOTheory.Signaling.proof_prop6_deriv_sigma_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:06:53.027987+00:00
-- url     : https://prove2.me/theorems/af144f09-1405-4a8d-b364-7c02ffc36bac
-- title:
--   Proof of Proposition 6: $d\alpha^*/d\sigma>0$
-- statement:
--   Let $\mu_L<\mu_H$, $\sigma>0$ and $\gamma>0$. The threshold $\alpha^*(\mu_H,\mu_L,\sigma,\gamma)$ of display (25), viewed as a function of $\sigma$ with $\mu_H,\mu_L,\gamma$ fixed, is differentiable at $\sigma$ and
--
--   $$
--   \frac{d\alpha^*}{d\sigma}>0 .
--   $$
--
--   Higher payoff volatility makes imitation less attractive to the risk-averse low type, so the high type can sell a larger share. Together with the independence of $\bar\alpha^T_H,\bar\alpha^E_H$ from $\sigma$, this gives the $\sigma$-interval of Proposition 6.
--
--   Differences from the source:
--
--   - encoding: §4's standing conditions μ_H > μ_L (p. 18), σ the standard deviation of ξ_i² (p. 18, p. 31), γ the risk aversion of a risk-averse entrepreneur (Assumption 1(i), p. 12) → hypotheses μL < μH, 0 < σ, 0 < γ; reason: the section states them once; as binders they exclude nothing the paper admits and keep Lean's junk values of √ and / out
--   - encoding: dα∗/dσ > 0 → 0 < deriv (fun s => alphaStar μH μL s γ) σ; reason: Mathlib's deriv is 0 where the function is not differentiable, so the inequality also asserts differentiability, as the paper's derivative presupposes
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), proof of Proposition 6, p. 32

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaStar

namespace ICOTheory.Signaling

/-- **Proof of Proposition 6: `dα*/dσ > 0`.**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), proof of Proposition 6, p. 32: "The result follows from the
facts that `dα*/dμ_L > 0`, `dα*/dσ > 0`, and `dᾱ^i_H/dμ_L = dᾱ^i_H/dσ = 0` for `i ∈ {E, T}`."

For `μ_L < μ_H`, `σ > 0`, `γ > 0`, the derivative of `s ↦ α*(μ_H, μ_L, s, γ)` at `s = σ` is
positive.

**Formalization Note.** `dα*/dσ > 0` is encoded as `0 < deriv (fun s => alphaStar μH μL s γ) σ`,
which also asserts differentiability at `σ`. `σ` is a standard deviation (p. 18), so `0 < σ`;
`α*` depends on `σ²`, so the derivative is negative at `σ < 0`. -/
theorem proof_prop6_deriv_sigma_pos {μH μL σ γ : ℝ} (hμ : μL < μH) (hσ : 0 < σ) (hγ : 0 < γ) :
    0 < deriv (fun s => alphaStar μH μL s γ) σ := by sorry

end ICOTheory.Signaling
