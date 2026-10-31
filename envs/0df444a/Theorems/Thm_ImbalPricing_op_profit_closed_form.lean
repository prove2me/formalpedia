-- Prove2me | Theorems.Thm_ImbalPricing_op_profit_closed_form
-- name    : ImbalPricing.op_profit_closed_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:05.999242+00:00
-- url     : https://prove2.me/theorems/eb429f30-5e6d-4f02-976a-7b0fe28d0f5e
-- title:
--   Expected OP profit in closed form (derived from Definition 4 and Eq. (20))
-- statement:
--   Under the standing assumptions of the market ($N\ge1$ LCGs with $\gamma^i>0$, $\gamma=\sum_j\gamma^j\le1$, $\alpha_2\ge\alpha_1\ge0$, mean-zero square-integrable forecast errors on a probability space, arbitrarily correlated), for every offer profile $d$ and every LCG $i$, with $D=\sum_{j=1}^N\gamma^jd^j$, the expected profit of LCG $i$ under the optimal imbalance price $p^i_{2,op}=p_1+\alpha_2H_2-\alpha_1L_1^i$ is
--
--   $$\Pi^i_{op}=\alpha_1\gamma^i(1-\gamma-D)-\alpha_2\gamma^id^iD+\alpha_1(\gamma^i)^2(1+d^i)d^i+\alpha_2\gamma^i\Big(\mathrm{Cov}(\epsilon,\nu^i)-\sum_{j=1}^N\gamma^j\,\mathrm{Cov}(\nu^j,\nu^i)\Big).$$
--
--   The profit is therefore a quadratic polynomial in the offers; the forecast errors enter only through a constant.
--
--   This closed form is not printed in the paper; it is derived from Definition 4 (Eq. (26)) and the expected-profit form of Eq. (20). The paper's proof of Theorem 5 (Online Appendix B.11) is not part of the source artifact.
--
--   Differences from the source:
--
--   - reading: profit Πⁱ = p₁L₁ⁱ + p₂ⁱL₂ⁱ (Eq. (9) prints no expectation; Eq. (20) prints p₁L₁ⁱ + E[p₂ⁱL₂ⁱ]) → expected profit Πⁱ_op = E[p₁L₁ⁱ + p^i_{2,op}L₂ⁱ]; reason: the offer is chosen in Stage 1 before ε, ν are realized, Eq. (20) and Proposition 1 take the expectation, and p₁, L₁ⁱ are deterministic, so both printed forms agree with this one
--   - reading: MC₂ 'continues only until the point where MC₂ reaches zero' (p.6) → prices and costs linear as in Eqs. (1)–(4), (8), (26), with no floor at zero; reason: every display and result of the paper uses the linear forms
--   - generalization: ε and νⁱ unbiased and bounded with ε ≥ −1, νⁱ ≥ −1 (pp.5–6) → ε and νⁱ have mean 0 and finite second moment (MemLp 2), with no bound; reason: the bounds only keep realized demand and production nonnegative and enter no formula; every bounded random variable is square integrable, so the source's case is included
--   - reading: expected productions γⁱ of N ≥ 1 LCGs with γ = Σγⁱ ≤ 1 (pp.5–6) → 0 < N, γⁱ > 0 for every i, Σγⁱ ≤ 1; reason: γⁱ is an expected production share and Eq. (10) divides by γⁱ, so γⁱ > 0 is part of the model
--   - generalization: offer profiles d with dⁱ ∈ [−1, 1/γ − 1] (p.7) → every real offer profile d; reason: the identity holds for all real d; the box profiles are a special case
--   - encoding: E[·], VAR(ɛ), Cov(νʲ, νⁱ) of random variables; LCGs i = 1, …, N → Bochner integrals against a probability measure μ, Mathlib's variance and covariance; LCGs indexed by Fin N; reason: Lean convention; under MemLp 2 these are the usual moments, same instances
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, derived from §7, Definition 4, Eq. (26), p.13 (PDF p.15) and Eq. (20), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ImbalPricing_Market
import Definitions.Def_ImbalPricing_OPMechanism

open MeasureTheory ProbabilityTheory

namespace ImbalPricing

/-- **Expected OP profit in closed form**, derived from Definition 4, Eq. (26), p.13 (PDF p.15)
and Eq. (20), p.11 (PDF p.13) of Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, *Optimal
Electricity Imbalance Pricing …*, MSOM Articles in Advance (2023). Under the standing
assumptions of §3.1, for every offer profile `d` and every LCG `i`, with `D = ∑_j γʲ dʲ` and
`γ = ∑_j γʲ`,
`Πⁱ_op = α₁ γⁱ (1 − γ − D) − α₂ γⁱ dⁱ D + α₁ (γⁱ)² (1 + dⁱ) dⁱ
         + α₂ γⁱ (Cov(ε, νⁱ) − ∑_j γʲ Cov(νʲ, νⁱ))`.

**Formalization Note.** A planning derivation (the paper's proof, Online Appendix B.11, is not
in the source artifact). `Var` and `Cov` are Mathlib's `variance` and `covariance`. -/
theorem op_profit_closed_form {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Market Ω N)
    (hM : M.Standing) (d : Fin N → ℝ) (i : Fin N) :
    M.profitOP d i =
      M.α₁ * M.γ i * (1 - M.share - ∑ j, M.γ j * d j)
        - M.α₂ * M.γ i * d i * (∑ j, M.γ j * d j)
        + M.α₁ * M.γ i ^ 2 * (1 + d i) * d i
        + M.α₂ * M.γ i *
            (covariance M.ε (M.ν i) M.μ - ∑ j, M.γ j * covariance (M.ν j) (M.ν i) M.μ) := by sorry

end ImbalPricing
