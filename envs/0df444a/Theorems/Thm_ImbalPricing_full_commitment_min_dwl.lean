-- Prove2me | Theorems.Thm_ImbalPricing_full_commitment_min_dwl
-- name    : ImbalPricing.full_commitment_min_dwl
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:17.994382+00:00
-- url     : https://prove2.me/theorems/4ccceae2-624a-448c-82ca-2d730e6ba60d
-- title:
--   Remark after Eq. (6): full commitment $d=0$ minimizes $\mathbb E[DWL]$
-- statement:
--   Under the standing assumptions of the market ($N\ge1$ LCGs with $\gamma^i>0$, $\gamma\le1$, $\alpha_2\ge\alpha_1\ge0$, mean-zero square-integrable forecast errors on a probability space), for every offer profile $d$,
--
--   $$\mathbb E[DWL(0)]\le\mathbb E[DWL(d)].$$
--
--   That is, when every LCG offers its total expected production in Stage 1 ($d^i=0$ for all $i$), the inefficiency caused by strategic offers is removed and only the part due to forecast errors remains. No condition on the correlation between $\epsilon$ and the $\nu^i$ is needed.
--
--   Differences from the source:
--
--   - reading: a sufficient (not necessary) condition to remove the inefficiency caused by the strategic behavior of LCGs occurs when ∀i : dⁱ = 0 → E[DWL] at d = 0 is at most E[DWL] at every offer profile d; reason: by (6) the strategic term (Σⱼγʲdʲ)² is nonnegative and vanishes at d = 0, so removing it is minimizing E[DWL]
--   - generalization: the observation is drawn from Eq. (6), which needs Cov(ε, νⁱ) = 0 (Lemma 1) → no covariance condition; reason: E[(ε − L₂)²] = E[(ε − Σγʲνʲ)²] + (Σγʲdʲ)² because the cross term has mean 0; the uncorrelated case is included
--   - generalization: ε and νⁱ unbiased and bounded with ε ≥ −1, νⁱ ≥ −1 (pp.5–6) → ε and νⁱ have mean 0 and finite second moment (MemLp 2), with no bound; reason: the bounds only keep realized demand and production nonnegative and enter no formula; every bounded random variable is square integrable, so the source's case is included
--   - reading: expected productions γⁱ of N ≥ 1 LCGs with γ = Σγⁱ ≤ 1 (pp.5–6) → 0 < N, γⁱ > 0 for every i, Σγⁱ ≤ 1; reason: γⁱ is an expected production share and Eq. (10) divides by γⁱ, so γⁱ > 0 is part of the model
--   - generalization: offer profiles d with dⁱ ∈ [−1, 1/γ − 1] (p.7) → every real offer profile d; reason: the identity holds for all real d; the box profiles are a special case
--   - encoding: E[·], VAR(ɛ), Cov(νʲ, νⁱ) of random variables; LCGs i = 1, …, N → Bochner integrals against a probability measure μ, Mathlib's variance and covariance; LCGs indexed by Fin N; reason: Lean convention; under MemLp 2 these are the usual moments, same instances
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §3.2, remark after Eq. (6), p.8 (PDF p.10)

import Mathlib
import Definitions.Def_ImbalPricing_Market
import Definitions.Def_ImbalPricing_ExpectedDWL

open MeasureTheory

namespace ImbalPricing

/-- **Full commitment minimizes the expected deadweight loss**, the remark after Eq. (6),
Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, *Optimal Electricity Imbalance Pricing …*, MSOM
Articles in Advance (2023), §3.2, p.8 (PDF p.10): "a sufficient (not necessary) condition to
remove the inefficiency caused by the strategic behavior of LCGs occurs when all LCGs offer
their total predicted production in Stage 1 (i.e., ∀i : dⁱ = 0)". Under the standing
assumptions of §3.1, `E[DWL]` at `d = 0` is at most `E[DWL]` at every offer profile `d`.

**Formalization Note.** No covariance condition between `ε` and the `νⁱ` is needed. The
inequality is stated for all real offer profiles, not only those in the strategy box. -/
theorem full_commitment_min_dwl {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Market Ω N)
    (hM : M.Standing) (d : Fin N → ℝ) :
    M.expectedDWL 0 ≤ M.expectedDWL d := by sorry

end ImbalPricing
