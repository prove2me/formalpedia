-- Prove2me | Theorems.Thm_ImbalPricing_eq_3
-- name    : ImbalPricing.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:26.629744+00:00
-- url     : https://prove2.me/theorems/378da3c7-f751-4cea-bf05-6dd2392c0706
-- title:
--   Eq. (3): the HCG's cost is $\alpha_1\mathcal H^2/2+(\alpha_2-\alpha_1)H_2^2/2$
-- statement:
--   For all real $\alpha_1,\alpha_2,H_1,H_2$, with $\mathcal H=H_1+H_2$, the cost of the high-cost generator defined as the area under its marginal-cost curves satisfies
--
--   $$C(H_1,H_2)=\int_0^{H_1}\alpha_1h\,dh+\int_{H_1}^{\mathcal H}\big[\alpha_1H_1+\alpha_2(h-H_1)\big]\,dh=\alpha_1\frac{\mathcal H^2}{2}+(\alpha_2-\alpha_1)\frac{H_2^2}{2}.$$
--
--   The first term is the cost of producing $\mathcal H$ at the Stage-1 marginal cost; the second is the extra cost of the adjustment, which is the deadweight loss.
--
--   **Formalization Note** The integrals are oriented, so the identity also covers $H_2<0$.
--
--   Differences from the source:
--
--   - generalization: H₁ ∈ [0, 1] (p.7) and α₂ ≥ α₁ ≥ 0 (p.5) → all real α₁, α₂, H₁, H₂; reason: the identity is algebraic in these parameters; the source's range is a special case
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §3.1.2, Eq. (3), p.6 (PDF p.8)

import Mathlib
import Definitions.Def_ImbalPricing_HCGCost

namespace ImbalPricing

/-- **Eq. (3)**, Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, *Optimal Electricity Imbalance
Pricing …*, MSOM Articles in Advance (2023), §3.1.2, p.6 (PDF p.8): the HCG's overall cost,
defined as the area under its marginal-cost curves, equals
`C(H₁, H₂) = α₁ 𝓗²/2 + (α₂ − α₁) H₂²/2` with `𝓗 = H₁ + H₂`.

**Formalization Note.** Stated for all real `α₁, α₂, H₁, H₂` (the paper has `α₂ ≥ α₁ ≥ 0` and
`H₁ ∈ [0, 1]`); `hcgCost` uses oriented interval integrals. -/
theorem eq_3 (α₁ α₂ H₁ H₂ : ℝ) :
    hcgCost α₁ α₂ H₁ H₂ = α₁ * (H₁ + H₂) ^ 2 / 2 + (α₂ - α₁) * H₂ ^ 2 / 2 := by sorry

end ImbalPricing
