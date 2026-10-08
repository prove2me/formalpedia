-- Prove2me | Theorems.Thm_MFGLimit_LDP_proposition_6_10
-- name    : MFGLimit.LDP.proposition_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:25.994008+00:00
-- url     : https://prove2.me/theorems/6f7938a6-cb61-4568-99f4-8bc5cc9ff5e6
-- title:
--   Proposition 6.10, p. 29 — σ₀ ≠ 0, K compact: lim_{δ↘0} inf_{K_δ}(J^{σ₀} + R(·₀|μ₀)) = inf_K (J^{σ₀} + R(·₀|μ₀))
-- statement:
--   Assume Condition 6.3 and that $\sigma$ is non-degenerate. If $\sigma_0\ne0$ and $K$ is a compact subset of $C([0,T];\mathcal P^1(\mathbb R^d))$, then
--
--   $$\lim_{\delta\searrow0}\inf_{\nu\in K_\delta}\big(J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)\big)=\inf_{\nu\in K}\big(J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)\big),$$
--
--   where $K_\delta=\{\nu:\inf_{\tilde\nu\in K}\sup_t\mathcal W_1(\tilde\nu_t,\nu_t)\le\delta\}$.
--
--   On compact sets the relaxed upper bound of Theorem 6.8 is therefore the standard one; this gives the compact-set upper bound of Theorem 3.10.
--
--   **Formalization Note** $\lim_{\delta\searrow0}$ is written as the supremum over $\delta>0$ (the infimum over $K_\delta$ is non-increasing in $\delta$). The case $\sigma_0=0$ of the proposition is the separate item `proposition_6_10_no_common_noise`.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 29, Proposition 6.10

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model
import Definitions.Def_MFGLimit_LDP_MeasureDeriv
import Definitions.Def_MFGLimit_LDP_Equations
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_MFGLimit_LDP_PathSpace
import Definitions.Def_MFGLimit_LDP_Action

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

/-- Proposition 6.10, p. 29, first claim (`σ₀ ≠ 0`, compact sets). -/
theorem proposition_6_10 {d d₀ : ℕ} (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (T : ℝ≥0) (hT : 0 < T) (hσ : σ.det ≠ 0) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (hb : DriftCond T btil)
    (μ₀ : Measure (MFGLimit.Conc.E d)) [IsProbabilityMeasure μ₀] (hexp : ExpMoments μ₀)
    (hσ₀ : σ₀ ≠ 0) (K : Set (PathP1 d T)) (hK : IsCompactD Dpath K) :
    (⨆ (δ : ℝ≥0∞) (_ : 0 < δ), ⨅ ν ∈ enlarge Dpath K δ, rateTilde σ σ₀ btil μ₀ ν) =
      ⨅ ν ∈ K, rateTilde σ σ₀ btil μ₀ ν := by sorry

end MFGLimit.LDP
