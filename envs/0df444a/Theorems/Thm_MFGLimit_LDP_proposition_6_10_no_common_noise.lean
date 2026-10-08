-- Prove2me | Theorems.Thm_MFGLimit_LDP_proposition_6_10_no_common_noise
-- name    : MFGLimit.LDP.proposition_6_10_no_common_noise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:37.30152+00:00
-- url     : https://prove2.me/theorems/90ec1078-299f-43f8-a5ec-0e676a73bd5b
-- title:
--   Proposition 6.10, p. 29 (σ₀ = 0) — the identity holds on closed sets, and m^n_X̃ satisfies a full LDP with a good rate function
-- statement:
--   In the setting of Theorem 6.8 (system (6.1), Condition 6.3, $\sigma$ non-degenerate), assume $\sigma_0=0$. Then
--
--   1. for every closed $F\subset C([0,T];\mathcal P^1(\mathbb R^d))$,
--   $$\lim_{\delta\searrow0}\inf_{\nu\in F_\delta}\big(J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)\big)=\inf_{\nu\in F}\big(J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)\big);$$
--   2. $\tilde J^{\sigma_0,\mu_0}$ is a good rate function, and $(m^n_{\tilde{\boldsymbol X}})_{n\ge1}$ satisfies the large deviation principle with it: the lower bound on open sets and $\limsup_n\frac1n\log\mathbb P(m^n_{\tilde{\boldsymbol X}}\in F)\le-\inf_F\tilde J^{\sigma_0,\mu_0}$ on closed sets.
--
--   Without common noise the weak LDP of Theorem 6.8 is a full LDP.
--
--   **Formalization Note** "Standard LDP with a good rate function" is stated as the three properties: good rate function, lower bound on open sets, upper bound on closed sets.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 29, Proposition 6.10 (second and third sentences)

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

/-- Proposition 6.10, p. 29, second and third claims (`σ₀ = 0`: closed sets, and a full LDP with
good rate function for (6.1)). -/
theorem proposition_6_10_no_common_noise {d d₀ : ℕ} (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (T : ℝ≥0) (hT : 0 < T) (hσ : σ.det ≠ 0) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (hb : DriftCond T btil)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d)
    (μ₀ : Measure (MFGLimit.Conc.E d)) (hset : IsSetup 𝔽 P W B X₀ μ₀) (hexp : ExpMoments μ₀)
    (hσ₀ : σ₀ = 0) (X : ∀ n, Fin n → Ω → CPath d T)
    (hX : ∀ n, IsInteractingSystem T 𝔽 P σ σ₀ W B X₀ btil (X n)) :
    (∀ F : Set (PathP1 d T), IsClosedD Dpath F →
      (⨆ (δ : ℝ≥0∞) (_ : 0 < δ), ⨅ ν ∈ enlarge Dpath F δ, rateTilde σ σ₀ btil μ₀ ν) =
        ⨅ ν ∈ F, rateTilde σ σ₀ btil μ₀ ν) ∧
      IsGoodRate (Dpath (d := d) (T := T)) (rateTilde σ σ₀ btil μ₀) ∧
      LDPLower P (flowEvent X) Dpath (rateTilde σ σ₀ btil μ₀) ∧
      LDPUpperClosed P (flowEvent X) Dpath (rateTilde σ σ₀ btil μ₀) := by sorry

end MFGLimit.LDP
