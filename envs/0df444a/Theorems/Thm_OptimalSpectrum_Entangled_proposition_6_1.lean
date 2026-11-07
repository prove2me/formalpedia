-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_proposition_6_1
-- name    : OptimalSpectrum.Entangled.proposition_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:41.21047+00:00
-- url     : https://prove2.me/theorems/1dc8670d-3a05-4886-bb0b-f85d748b990d
-- title:
--   Proposition 6.1 — recovery on the full Chebyshev interval
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $d\ge1$, $L>0$, $K\ge1$, let $\alpha\in Z_d$ be the true spectrum, and let $\widehat M_1,\dots,\widehat M_K$ be real estimates on a probability space, unbiased for $\sum_i\alpha_i^m$ and with finite variances (no independence assumed); put $\widehat M_0=d$ and $\widehat F_p=\sum_mp_m\widehat M_m$. If $\widehat z$ is a measurable selection of
--
--   $$\widehat z\in\arg\min_{z\in Z_d}\sum_{k=1}^K\frac1{k^2}\Big(\widehat F_{\phi_k}-\sum_{i=1}^d\phi_k(z_i)\Big)^2,$$
--
--   then
--
--   $$\mathbb E\,d_{\mathrm{TV}}(\alpha,\widehat z)\le C\frac{\sqrt{dL}}K+CL\sum_{k=1}^K\frac{\mathrm{Var}(\widehat F_{\phi_k})}{k^2}.$$
--
--   Here $\mathrm{Var}(\widehat F_p)=\mathbb E(\widehat F_p-\sum_ip(\alpha_i))^2$ (Eq. (18)). The first term is the approximation error of the full-interval basis, small near the endpoints, the second the propagated estimation error; Section 8 balances them.
--
--   Differences from the source:
--   - encoding: E d_TV(α, ẑ) for ẑ ∈ arg min → the bound for every measurable selection ẑ of the arg min; reason: the expectation is undefined otherwise; every minimizer satisfies the pointwise bound the proof uses, so only undefined cases are excluded
--   - encoding: "unbiased real estimates … with finite variances", Var(F̂_p) → MemLp 2 and E M̂_m = Σ α_i^m for 1 ≤ m ≤ K; Var(F̂_p) as Eq. (18); reason: Eq. (18) is the page's own expression of the variance under unbiasedness
--   - encoding: d ⩾ 1, L > 0, K ⩾ 1, α ∈ Z_d stated once in the §6 Setup → binders of the statement; reason: standing assumptions of the section
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Proposition 6.1, Eq. (21), p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38
import Definitions.Def_OptimalSpectrum_Entangled_Zd
import Definitions.Def_OptimalSpectrum_Entangled_phiPoly
import Definitions.Def_OptimalSpectrum_Entangled_momentVar
import Definitions.Def_OptimalSpectrum_Entangled_IsUnbiasedMoments
import Definitions.Def_OptimalSpectrum_Entangled_IsLSEstimator

open MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P38 (tv)

namespace OptimalSpectrum.Entangled

/-- **Proposition 6.1 (Recovery on the full Chebyshev interval).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Proposition 6.1, printed p. 14 (PDF p. 16): "For 1 ⩽ k ⩽ K, define ϕ_k(x) := T_k((x − L/2)/(L/2)) − (−1)^k. (20) Note that ϕ_k(0) = 0. Define the spectrum estimator as ẑ_full ∈ arg min_(z∈Z_d) ∑_(k=1)^K (1/k²)(F̂_(ϕ_k) − ∑_(i=1)^d ϕ_k(z_i))². Then E d_TV(α, ẑ_full) ⩽ C√(dL)/K + CL ∑_(k=1)^K Var(F̂_(ϕ_k))/k². (21)"

Setup (§6, printed p. 13): `d ≥ 1`, `L > 0`, `K ≥ 1`, the true spectrum `α ∈ Z_d`, and real estimates
`M̂₁, …, M̂_K` on a probability space that are unbiased for `∑ᵢ αᵢ^m` with finite variances ("No
independence assumption on the moment estimates is needed"). `F̂_p = ∑ p_m M̂_m` with `M̂₀ = d`, and
`Var(F̂_p)` is Eq. (18).

**Formalization Note.** `C` is one universal constant, chosen before `d, L, K`. `ẑ` is any
selection from the arg min that is measurable, so that its expectation is defined; every minimizer
satisfies the pointwise bound the proof uses, so this excludes only undefined cases. -/
theorem proposition_6_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ L : ℝ, 0 < L → ∀ K : ℕ, 1 ≤ K →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (α : Fin d → ℝ) (Mhat : ℕ → Ω → ℝ) (zhat : Ω → Fin d → ℝ),
        α ∈ Zd d L → IsUnbiasedMoments μ K Mhat α → IsLSEstimator d L K Mhat (phiPoly L) zhat →
        Measurable zhat →
        ∫ ω, tv α (zhat ω) ∂μ ≤
          C * Real.sqrt (d * L) / K +
            C * L * ∑ k ∈ Finset.Icc 1 K, momentVar μ d K Mhat α (phiPoly L k) / (k : ℝ) ^ 2 := by sorry

end OptimalSpectrum.Entangled
