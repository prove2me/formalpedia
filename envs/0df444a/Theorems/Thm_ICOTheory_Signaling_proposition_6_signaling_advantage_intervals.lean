-- Prove2me | Theorems.Thm_ICOTheory_Signaling_proposition_6_signaling_advantage_intervals
-- name    : ICOTheory.Signaling.proposition_6_signaling_advantage_intervals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:08:03.761059+00:00
-- url     : https://prove2.me/theorems/27a6d0fc-786b-41bb-a841-c3200ee6aba9
-- title:
--   Proposition 6: tokens have a signaling advantage over equity iff $\mu_L\in[\mu_l,\mu_u)$, iff $\sigma\in[\sigma_l,\sigma_u)$
-- statement:
--   Consider the model of §4: $C(q)=C$, $p_e=0$ and Assumption 1, so the revenue of a type-$i$ venture is $R_i=\xi_i^2/4$ with $\xi_i^2$ normal of mean $\mu_i$ and standard deviation $\sigma$. Let $\gamma>0$ be the entrepreneur's risk aversion, $I>0$ the initial investment, $C\ge0$ the fixed production cost, and assume the venture is sufficiently profitable (p. 10):
--
--   $$
--   C+I<\frac{\mu_H}{4}.
--   $$
--
--   Write $\alpha^*$ for the threshold (25) and $\bar\alpha^T_H=I/(\mu_H/4)$, $\bar\alpha^E_H=I/(\mu_H/4-C)$ for the minimal shares (21). Then:
--
--   1. for every $\sigma>0$ there are thresholds $\mu_l<\mu_u$ such that for every $\mu_L<\mu_H$,
--   $$
--   \bar\alpha^T_H\le\alpha^*<\bar\alpha^E_H\iff \mu_l\le\mu_L<\mu_u ;
--   $$
--   2. for every $\mu_L<\mu_H$ there are thresholds $\sigma_l<\sigma_u$ such that for every $\sigma>0$,
--   $$
--   \bar\alpha^T_H\le\alpha^*<\bar\alpha^E_H\iff \sigma_l\le\sigma<\sigma_u .
--   $$
--
--   Tokens therefore allow separation where equity does not exactly for moderate venture heterogeneity and for moderate payoff volatility. When $C=0$ the two shares coincide, the advantage never holds, and the thresholds exist only vacuously, outside the parameter domain.
--
--   Differences from the source:
--
--   - reading: one chain "µl ≤ µL < µu ⇐⇒ σl ≤ σ < σu" → two conjoined characterizations: for each σ > 0, thresholds µl < µu (not depending on µL) with the iff over all µL < µH; for each µL < µH, thresholds σl < σu (not depending on σ) with the iff over all σ > 0; reason: the discussion after the proposition (p. 22) treats heterogeneity "keeping µH fixed" and volatility separately, and the proof (p. 32) gives one derivative per parameter
--   - reading: standing assumption p. 10: αER + (1 − α)R − C − I > 0 "with probability close to one" → C + I < μH / 4; reason: for the high type's normal payoff this is mean µH/4 − C − I > 0, equivalently ᾱE_H < 1; without it the σ half is false (µH = 4, C = 1/2, I = 3/5, γ = 1, µL = 0: the advantage holds for all large σ)
--   - reading: I the investment of an entrepreneur without wealth (p. 5), C a production cost (Assumption 1(iv), p. 12), γ the coefficient of absolute risk aversion of a risk-averse entrepreneur (p. 12) → 0 < I, 0 ≤ C, 0 < γ; reason: the model's standing sign conditions; with I ≤ 0 the µL-set is unbounded below, and γ = 0 makes (25) a division by zero
--   - generalization: µL in the model's range below µH; σ a volatility of the model → every real µL < µH and every real σ > 0; reason: no further bound on µL or σ is imposed; thresholds that work on the larger domain work, with the same iff, on any subdomain
--   - encoding: ξ_i² ≈ N(µ_i, σ), σ a common volatility → σ a positive real, entering only through (25); reason: σ is the standard deviation (the proof of Proposition 5, p. 31, produces γ²(1 − α)²σ²/32; p. 29 writes X ∼ N(m, s) for m + sZ)
--   - encoding: C(q) = C, p_e = 0, Assumption 1; ERj; "signaling advantage" → statements about the closed forms (21), (25) with ERj = μj/4; SignalingAdvantage := ᾱT_H ≤ α∗ < ᾱE_H; reason: the paper derives (21) and (25) under these hypotheses and defines the advantage by the inequality ("i.e."), so they have no further content
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), Proposition 6, p. 22; funding assumption, §2.2, p. 10; setting, §4, p. 18

import Mathlib
import Definitions.Def_ICOTheory_Signaling_SignalingAdvantage

namespace ICOTheory.Signaling

/-- **Proposition 6: tokens have a signaling advantage over equity iff `μ_L ∈ [μ_l, μ_u)`, iff
`σ ∈ [σ_l, σ_u)`.**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), Proposition 6, p. 22: "Suppose `C(q) = C`, `p_e = 0`, and
Assumption 1 holds. There exist thresholds `μ_l < μ_u` and `σ_l < σ_u` such that tokens have a
signaling advantage over equity, i.e., `ᾱ^T_H ≤ α* < ᾱ^E_H`, if and only if
`μ_l ≤ μ_L < μ_u ⟺ σ_l ≤ σ < σ_u`."

Let `γ > 0`, `I > 0`, `C ≥ 0` and `C + I < μ_H/4`. Then
1. for every `σ > 0` there are `μ_l < μ_u` such that, for every `μ_L < μ_H`, the advantage holds
   iff `μ_l ≤ μ_L < μ_u`;
2. for every `μ_L < μ_H` there are `σ_l < σ_u` such that, for every `σ > 0`, the advantage holds
   iff `σ_l ≤ σ < σ_u`.

**Formalization Note.**
* The chain "`μ_l ≤ μ_L < μ_u ⟺ σ_l ≤ σ < σ_u`" is read as two one-parameter
  characterizations, each with the other parameters fixed (the discussion after the
  proposition, p. 22, treats heterogeneity "keeping `μ_H` fixed" and volatility separately,
  and the proof, p. 32, gives one derivative per parameter). The thresholds of (1) may depend
  on `σ, μ_H, γ, I, C` but not on `μ_L`; those of (2) not on `σ`.
* `C + I < μ_H/4` is the standing assumption of p. 10 ("the venture is sufficiently profitable
  so that in equilibrium `α𝔼R + (1 − α)R − C − I > 0` with probability close to one"): with the
  normal revenue of §4 this is mean `μ_H/4 − C − I > 0`. It is equivalent to `ᾱ^E_H < 1`; without
  it (2) is false (`μ_H = 4`, `C = 1/2`, `I = 3/5`, `γ = 1`, `μ_L = 0`: the advantage holds for
  every large `σ`).
* `I > 0` (the investment of an entrepreneur without wealth, p. 5), `C ≥ 0` (a cost,
  Assumption 1(iv), p. 12) and `γ > 0` (risk aversion, p. 12) are the model's standing
  conditions. `σ > 0` is a standard deviation; `μ_L < μ_H` is §4's `μ_H > μ_L` (p. 18).
* At `C = 0`, `ᾱ^T_H = ᾱ^E_H`, the advantage never holds and the thresholds exist only
  vacuously, outside the domain.
* `C(q) = C`, `p_e = 0` and Assumption 1 are the hypotheses under which the paper derives the
  closed forms (21) and (25); the statement is about those closed forms. -/
theorem proposition_6_signaling_advantage_intervals {μH γ I C : ℝ}
    (hγ : 0 < γ) (hI : 0 < I) (hC : 0 ≤ C) (hfund : C + I < μH / 4) :
    (∀ σ : ℝ, 0 < σ → ∃ μl μu : ℝ, μl < μu ∧
        ∀ μL : ℝ, μL < μH → (SignalingAdvantage μH μL σ γ I C ↔ μl ≤ μL ∧ μL < μu)) ∧
    (∀ μL : ℝ, μL < μH → ∃ σl σu : ℝ, σl < σu ∧
        ∀ σ : ℝ, 0 < σ → (SignalingAdvantage μH μL σ γ I C ↔ σl ≤ σ ∧ σ < σu)) := by sorry

end ICOTheory.Signaling
