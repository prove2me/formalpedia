-- Prove2me | Theorems.Thm_ImbalPricing_eq_4
-- name    : ImbalPricing.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:31.908225+00:00
-- url     : https://prove2.me/theorems/5344cb21-a9a0-4c1c-9eeb-0f97eefaa38c
-- title:
--   Eq. (4): $DWL=(\alpha_2-\alpha_1)H_2^2/2$, and the cost of a given total is least at $H_2=0$
-- statement:
--   For all real $\alpha_1,\alpha_2,H_1,H_2$, with $\mathcal H=H_1+H_2$:
--
--   1. the deadweight loss satisfies
--   $$DWL=C(H_1,H_2)-C(\mathcal H,0)=(\alpha_2-\alpha_1)\frac{H_2^2}{2};$$
--   2. if $\alpha_1\le\alpha_2$, then the minimum cost of producing a given total $\mathcal H$ is attained by scheduling it all in Stage 1:
--   $$C(\mathcal H,0)\le C(H_1,H_2).$$
--
--   Part 2 is why the deadweight loss measures the inefficiency of an outcome: with inelastic demand the total $\mathcal H$ is fixed, and every unit moved to Stage 2 costs more.
--
--   Differences from the source:
--
--   - generalization: H₁ ∈ [0, 1] and α₂ ≥ α₁ ≥ 0 → all real H₁, H₂; part 1 for all real α₁, α₂, part 2 under α₁ ≤ α₂ only; reason: part 1 is algebraic and part 2 uses only α₂ − α₁ ≥ 0; the source's range is a special case
--   - reading: the minimum possible cost of production happens when H2 = 0 → C(H₁ + H₂, 0) ≤ C(H₁, H₂) for all H₁, H₂; reason: demand is inelastic, so the total 𝓗 = H₁ + H₂ is fixed and the comparison is over its splits
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §3.2, Eq. (4), p.7 (PDF p.9)

import Mathlib
import Definitions.Def_ImbalPricing_HCGCost

namespace ImbalPricing

/-- **Eq. (4)**, Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, *Optimal Electricity Imbalance
Pricing …*, MSOM Articles in Advance (2023), §3.2, p.7 (PDF p.9):

1. `DWL = C(H₁, H₂) − C(𝓗, 0) = (α₂ − α₁) H₂²/2`;
2. when `α₁ ≤ α₂`, "the minimum possible cost of production happens when `H₂ = 0`": for a
   given total `𝓗 = H₁ + H₂`, `C(𝓗, 0) ≤ C(H₁, H₂)`.

**Formalization Note.** Stated for all real `H₁, H₂`; part 2 assumes only `α₁ ≤ α₂`
(the paper's standing assumption is `α₂ ≥ α₁ ≥ 0`). -/
theorem eq_4 (α₁ α₂ H₁ H₂ : ℝ) :
    dwl α₁ α₂ H₁ H₂ = (α₂ - α₁) * H₂ ^ 2 / 2 ∧
      (α₁ ≤ α₂ → hcgCost α₁ α₂ (H₁ + H₂) 0 ≤ hcgCost α₁ α₂ H₁ H₂) := by sorry

end ImbalPricing
