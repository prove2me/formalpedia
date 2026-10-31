-- Prove2me | Theorems.Thm_ImbalPricing_lemma_1
-- name    : ImbalPricing.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:12.635453+00:00
-- url     : https://prove2.me/theorems/74d79c2f-ee3b-4a1c-a2c7-208d8d25cbe4
-- title:
--   Lemma 1 (corrected: $\epsilon$ uncorrelated with $\sum_i\gamma^i\nu^i$): the expected deadweight loss (5)–(6)
-- statement:
--   Assume the standing assumptions of the market: $N\ge1$ LCGs with $\gamma^i>0$, $\gamma=\sum_i\gamma^i\le1$, $\alpha_2\ge\alpha_1\ge0$, and mean-zero square-integrable forecast errors $\epsilon,\nu^1,\dots,\nu^N$ on a probability space. For every offer profile $d$:
--
--   1. the expected deadweight loss is
--   $$\mathbb E[DWL]=\frac{\alpha_2-\alpha_1}{2}\,\mathbb E\big[(\epsilon-L_2)^2\big];$$
--   2. if moreover $\sum_{i=1}^N\gamma^i\,\mathrm{Cov}(\epsilon,\nu^i)=0$ (that is, $\epsilon$ is uncorrelated with $\sum_i\gamma^i\nu^i$; in particular when $\mathrm{Cov}(\epsilon,\nu^i)=0$ for every $i$), then
--   $$\mathbb E[DWL]=\frac{\alpha_2-\alpha_1}{2}\big(\mathrm{Var}(\epsilon)+\mathbb E[L_2^2]\big)\qquad(5)$$
--   and
--   $$\mathbb E[DWL]=\frac{\alpha_2-\alpha_1}{2}\Big(\sum_{j=1}^N\sum_{i=1}^N\gamma^j\gamma^id^jd^i+\mathrm{Var}(\epsilon)+\sum_{j=1}^N\sum_{i=1}^N\gamma^j\gamma^i\,\mathrm{Cov}(\nu^j,\nu^i)\Big).\qquad(6)$$
--
--   Equation (6) separates the inefficiency caused by the LCGs' strategic offers (the first double sum, which is $(\sum_j\gamma^jd^j)^2$) from the part caused by forecast errors.
--
--   Differences from the source:
--
--   - correction: the second equality of (5) and Eq. (6) hold with no condition on ε and νⁱ → they are stated under Σᵢγⁱ Cov(ε, νⁱ) = 0; the first equality of (5) is unconditional; reason: no section assumes ε uncorrelated with νⁱ in the general setting, and the second equality drops −2E[εL₂] = −2Σᵢγⁱ Cov(ε, νⁱ), so this condition is exactly what it needs (it holds when every Cov(ε, νⁱ) = 0): N = 1, γ¹ = 1/2, α₁ = 1, α₂ = 3, ε = ν¹ = ±1/2 with probability 1/2 each (mean 0, bounded, ≥ −1) gives E[DWL] = 1/16 at d = 0, while (6) gives 5/16
--   - reading: the product dʲ₁dⁱ₁ in (6) → dʲdⁱ; reason: the subscript 1 appears nowhere else on d, and Eq. (11) is (6) at Theorem 1's offers under this reading
--   - generalization: ε and νⁱ unbiased and bounded with ε ≥ −1, νⁱ ≥ −1 (pp.5–6) → ε and νⁱ have mean 0 and finite second moment (MemLp 2), with no bound; reason: the bounds only keep realized demand and production nonnegative and enter no formula; every bounded random variable is square integrable, so the source's case is included
--   - reading: expected productions γⁱ of N ≥ 1 LCGs with γ = Σγⁱ ≤ 1 (pp.5–6) → 0 < N, γⁱ > 0 for every i, Σγⁱ ≤ 1; reason: γⁱ is an expected production share and Eq. (10) divides by γⁱ, so γⁱ > 0 is part of the model
--   - generalization: offer profiles d with dⁱ ∈ [−1, 1/γ − 1] (p.7) → every real offer profile d; reason: the identity holds for all real d; the box profiles are a special case
--   - encoding: E[·], VAR(ɛ), Cov(νʲ, νⁱ) of random variables; LCGs i = 1, …, N → Bochner integrals against a probability measure μ, Mathlib's variance and covariance; LCGs indexed by Fin N; reason: Lean convention; under MemLp 2 these are the usual moments, same instances
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §3.2, Lemma 1, Eqs. (5)–(6), p.8 (PDF p.10)

import Mathlib
import Definitions.Def_ImbalPricing_Market
import Definitions.Def_ImbalPricing_ExpectedDWL

open MeasureTheory ProbabilityTheory

namespace ImbalPricing

/-- **Lemma 1** (corrected: `ε` uncorrelated with `∑ γⁱνⁱ`), Ghiassi-Farrokhfal, Belo,
Hesamzadeh, Bunn, *Optimal Electricity Imbalance Pricing …*, MSOM Articles in Advance (2023),
§3.2, Eqs. (5)–(6), p.8 (PDF p.10). Under the standing assumptions of §3.1, for every offer
profile `d`:

1. `E[DWL] = ((α₂ − α₁)/2) E[(ε − L₂)²]` (first equality of (5));
2. if `∑_i γⁱ Cov(ε, νⁱ) = 0` (that is, `Cov(ε, ∑_i γⁱνⁱ) = 0`), then
   `E[DWL] = ((α₂ − α₁)/2) (Var(ε) + E[L₂²])` (second equality of (5)) and
   `E[DWL] = ((α₂ − α₁)/2) (∑_j ∑_i γʲγⁱ dʲdⁱ + Var(ε) + ∑_j ∑_i γʲγⁱ Cov(νʲ, νⁱ))` (6).

**Formalization Note.** The printed second equality of (5) and (6) need
`∑_i γⁱ Cov(ε, νⁱ) = 0`, which the paper does not state (the second equality drops
`−2 E[ε L₂] = −2 ∑_i γⁱ Cov(ε, νⁱ)`; the condition holds in particular when `ε` is uncorrelated
with every `νⁱ`): with `N = 1`, `γ¹ = 1/2`, `α₁ = 1`, `α₂ = 3`,
`ε = ν¹ = ±1/2` with probability `1/2` each, `E[DWL] = 1/16` at `d = 0` while (6) gives `5/16`.
The printed `d^j_1 d^i_1` is read as `dʲdⁱ`. Expectations are Bochner integrals; `Var` and `Cov`
are Mathlib's `variance` and `covariance`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Market Ω N) (hM : M.Standing)
    (d : Fin N → ℝ) :
    M.expectedDWL d = (M.α₂ - M.α₁) / 2 * ∫ ω, (M.ε ω - M.L2 d ω) ^ 2 ∂M.μ ∧
      ((∑ i, M.γ i * covariance M.ε (M.ν i) M.μ = 0) →
        M.expectedDWL d =
            (M.α₂ - M.α₁) / 2 * (variance M.ε M.μ + ∫ ω, M.L2 d ω ^ 2 ∂M.μ) ∧
          M.expectedDWL d =
            (M.α₂ - M.α₁) / 2 *
              (∑ j, ∑ i, M.γ j * M.γ i * d j * d i + variance M.ε M.μ +
                ∑ j, ∑ i, M.γ j * M.γ i * covariance (M.ν j) (M.ν i) M.μ)) := by sorry

end ImbalPricing
