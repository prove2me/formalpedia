-- Prove2me | Theorems.Thm_ICOTheory_Signaling_eq_25_alphaStar_mem_Ioo
-- name    : ICOTheory.Signaling.eq_25_alphaStar_mem_Ioo
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-29T18:05:15.699556+00:00
-- url     : https://prove2.me/theorems/f4909708-5476-4a10-bbe2-80017e535e2d
-- title:
--   (25): the signaling threshold $\alpha^*$ lies in $(0,1)$
-- statement:
--   Let $\mu_L<\mu_H$, $\sigma>0$ and $\gamma>0$. Then the threshold
--
--   $$
--   \alpha^*=\frac{4\mu_H-4\mu_L+\sigma^2\gamma-\sqrt{(4\mu_H-4\mu_L)(4\mu_H-4\mu_L+2\sigma^2\gamma)}}{\sigma^2\gamma}
--   $$
--
--   satisfies $0<\alpha^*<1$.
--
--   This is the claim "$\in(0,1)$" attached to display (25): in the least-cost separating equilibrium the high type sells a proper, nonempty share of its venture.
--
--   Differences from the source:
--
--   - encoding: §4's standing conditions μ_H > μ_L (p. 18), σ the standard deviation of ξ_i² (p. 18, p. 31), γ the risk aversion of a risk-averse entrepreneur (Assumption 1(i), p. 12) → hypotheses μL < μH, 0 < σ, 0 < γ; reason: the section states them once; as binders they exclude nothing the paper admits and keep Lean's junk values of √ and / out
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), §4, display (25), p. 20

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaStar

namespace ICOTheory.Signaling

/-- **Display (25): the signaling threshold `α*` lies in `(0, 1)`.**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), §4, display (25), p. 20:
`α* ≡ (4μ_H − 4μ_L + σ²γ − √((4μ_H − 4μ_L)(4μ_H − 4μ_L + 2σ²γ)))/(σ²γ) ∈ (0, 1)`.

For `μ_L < μ_H` (§4, p. 18: `μ_H > μ_L`), `σ > 0` and `γ > 0`, `0 < α* < 1`.

**Formalization Note.** `σ` is the standard deviation of `ξ_i²` and `γ` the risk aversion of
the risk-averse entrepreneur (Assumption 1(i), p. 12); these are §4's standing conditions.
At `μ_L = μ_H` the formula equals `1`, so the strict inequality `μL < μH` is needed. -/
theorem eq_25_alphaStar_mem_Ioo {μH μL σ γ : ℝ} (hμ : μL < μH) (hσ : 0 < σ) (hγ : 0 < γ) :
    0 < alphaStar μH μL σ γ ∧ alphaStar μH μL σ γ < 1 := by sorry

end ICOTheory.Signaling
