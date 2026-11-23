-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_Supplement_limit_infinity
-- name    : OTSensitivity.MaxFun.Supplement.limit_infinity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:28:30.856245+00:00
-- url     : https://prove2.me/theorems/5a2ae987-7056-4577-b2ce-366ec9f5475d
-- title:
--   Proof of Theorem 19 — $K_\varepsilon(\nu,\nu')\to\mathcal K(\nu\times\nu')$ as $\varepsilon\to\infty$
-- statement:
--   Let $\mathsf Y$ be a Polish space with its Borel σ-algebra and let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be a cost that is continuous and vanishes exactly on the diagonal, $k(y,y')=0\iff y=y'$. For probability measures $\nu,\nu'$ on $\mathsf Y$, $\Pi(\nu,\nu')$ is the set of couplings, $K(\nu,\nu')=\inf_{\pi\in\Pi(\nu,\nu')}\int k\,d\pi$ is the optimal transport cost (1), and for $\varepsilon\ge0$ the **entropic OT functional** (8) is
--
--   $$K_\varepsilon(\nu,\nu')=\inf_{\pi\in\Pi(\nu,\nu')}\int\!\!\int k(y,y')\,d\pi(y,y')+\varepsilon\,\mathrm{KL}(\pi\,|\,\nu\times\nu'),$$
--
--   where $\mathrm{KL}$ is the Kullback–Leibler divergence (7).
--
--   For all probability measures $\nu,\nu'$ on $\mathsf Y$,
--
--   $$\lim_{\varepsilon\to\infty}K_\varepsilon(\nu,\nu')=\int\!\!\int k(y,y')\,d\nu(y)\,d\nu'(y')=\mathcal K(\nu\times\nu')$$
--
--   in $[0,+\infty]$; the limit may be $+\infty$. As the regularization grows, the entropic optimal plan approaches the product plan $\nu\times\nu'$, whose cost is $\mathcal K(\nu\times\nu')$. Applied to $\nu'=\nu_x$ and integrated against $\mu$, it gives Theorem 19.
--
--   **Formalization Note** $\varepsilon$ ranges over `ℝ≥0` along `atTop`; the limit is in `ℝ≥0∞` with its order topology.
--
--   Differences from the source:
--   - generalization: $K_\varepsilon(\nu,\nu_x)\to\mathcal K(\nu\times\nu_x)$ for the law $\nu$ of $Y$ and its conditional laws $\nu_x$ → every pair of probability measures $\nu,\nu'$ on $\mathsf Y$; reason: the page's instance is $\nu'=\nu_x$; the argument does not use the relation between $\nu$ and $\nu_x$
--   - reading: the result names no cost assumption, or only "k continuous" → `IsCost k`: $k$ continuous into $[0,+\infty]$ and $k(y,y')=0\iff y=y'$; reason: this is the standing cost assumption of §3.1 (p. 9), under which every result of the section is stated
--   - generalization: the output space is a subset of $\mathbb R^{n_Y}$ (p. 4) → the output space $\mathsf Y$ is an arbitrary Polish space with its Borel σ-algebra; reason: closed subsets of Euclidean space are Polish, so the paper's setting is an instance; the same convention as the published base mission
--   - encoding: values of $k$, $K$, $K_\varepsilon$, KL in $[0,+\infty]$ → values in `ℝ≥0∞`; KL is Mathlib's `InformationTheory.klDiv`; reason: for probability measures `klDiv` is $+\infty$ off absolute continuity and $\int\log\frac{d\pi}{d\vartheta}\,d\pi$ otherwise, which is (7); same instances
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Theorem 19, p. 38

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting
import Definitions.Def_OTSensitivity_MaxFun_Supplement_Entropic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.MaxFun.Supplement

/-- Proof of Theorem 19, p. 38: as `ε → ∞`, `K_ε(ν, ν') → 𝒦(ν × ν') = ∫∫ k(y, y') dν(y) dν'(y')`
in `[0, +∞]`, for all probability measures `ν, ν'` on `𝒴`. -/
theorem limit_infinity {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴]
    [BorelSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ν : Measure 𝒴) [IsProbabilityMeasure ν] (ν' : Measure 𝒴) [IsProbabilityMeasure ν'] :
    Tendsto (fun ε : ℝ≥0 => entropicTransportCost k ε ν ν') atTop
      (𝓝 (∫⁻ y, ∫⁻ y', k y y' ∂ν' ∂ν)) := by sorry

end OTSensitivity.MaxFun.Supplement
