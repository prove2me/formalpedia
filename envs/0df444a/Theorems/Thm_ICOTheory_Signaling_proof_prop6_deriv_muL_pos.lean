-- Prove2me | Theorems.Thm_ICOTheory_Signaling_proof_prop6_deriv_muL_pos
-- name    : ICOTheory.Signaling.proof_prop6_deriv_muL_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:06:21.808569+00:00
-- url     : https://prove2.me/theorems/0f93e487-df7a-4ad0-bce3-d78f54ad1693
-- title:
--   Proof of Proposition 6: $d\alpha^*/d\mu_L>0$
-- statement:
--   Let $\mu_L<\mu_H$, $\sigma>0$ and $\gamma>0$. The threshold $\alpha^*(\mu_H,\mu_L,\sigma,\gamma)$ of display (25), viewed as a function of $\mu_L$ with $\mu_H,\sigma,\gamma$ fixed, is differentiable at $\mu_L$ and
--
--   $$
--   \frac{d\alpha^*}{d\mu_L}>0 .
--   $$
--
--   As the two types become more alike, the high type can sell a larger share without being imitated. Together with the independence of $\bar\alpha^T_H,\bar\alpha^E_H$ from $\mu_L$, this gives the $\mu_L$-interval of Proposition 6.
--
--   Differences from the source:
--
--   - encoding: §4's standing conditions μ_H > μ_L (p. 18), σ the standard deviation of ξ_i² (p. 18, p. 31), γ the risk aversion of a risk-averse entrepreneur (Assumption 1(i), p. 12) → hypotheses μL < μH, 0 < σ, 0 < γ; reason: the section states them once; as binders they exclude nothing the paper admits and keep Lean's junk values of √ and / out
--   - encoding: dα∗/dµL > 0 → 0 < deriv (fun x => alphaStar μH x σ γ) μL; reason: Mathlib's deriv is 0 where the function is not differentiable, so the inequality also asserts differentiability, as the paper's derivative presupposes
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), proof of Proposition 6, p. 32

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaStar

namespace ICOTheory.Signaling

/-- **Proof of Proposition 6: `dα*/dμ_L > 0`.**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), proof of Proposition 6, p. 32: "The result follows from the
facts that `dα*/dμ_L > 0`, `dα*/dσ > 0`, and `dᾱ^i_H/dμ_L = dᾱ^i_H/dσ = 0` for `i ∈ {E, T}`."

For `μ_L < μ_H`, `σ > 0`, `γ > 0`, the derivative of `x ↦ α*(μ_H, x, σ, γ)` at `x = μ_L` is
positive.

**Formalization Note.** `dα*/dμ_L > 0` is encoded as `0 < deriv (fun x => alphaStar μH x σ γ) μL`.
Mathlib's `deriv` is `0` where the function is not differentiable, so this also asserts
differentiability at `μ_L`; it is stronger than strict monotonicity. -/
theorem proof_prop6_deriv_muL_pos {μH μL σ γ : ℝ} (hμ : μL < μH) (hσ : 0 < σ) (hγ : 0 < γ) :
    0 < deriv (fun x => alphaStar μH x σ γ) μL := by sorry

end ICOTheory.Signaling
