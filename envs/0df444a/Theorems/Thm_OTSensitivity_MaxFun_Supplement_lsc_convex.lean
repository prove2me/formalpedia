-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_Supplement_lsc_convex
-- name    : OTSensitivity.MaxFun.Supplement.lsc_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:27:04.139653+00:00
-- url     : https://prove2.me/theorems/02aca922-8a2e-4e68-b04c-15c269ee2740
-- title:
--   Proof of Theorem 11 — $K_\varepsilon(\nu,\cdot)$ is lower semicontinuous under weak convergence and convex
-- statement:
--   Let $\mathsf Y$ be a Polish space with its Borel σ-algebra and let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be a cost that is continuous and vanishes exactly on the diagonal, $k(y,y')=0\iff y=y'$. For probability measures $\nu,\nu'$ on $\mathsf Y$, $\Pi(\nu,\nu')$ is the set of couplings, $K(\nu,\nu')=\inf_{\pi\in\Pi(\nu,\nu')}\int k\,d\pi$ is the optimal transport cost (1), and for $\varepsilon\ge0$ the **entropic OT functional** (8) is
--
--   $$K_\varepsilon(\nu,\nu')=\inf_{\pi\in\Pi(\nu,\nu')}\int\!\!\int k(y,y')\,d\pi(y,y')+\varepsilon\,\mathrm{KL}(\pi\,|\,\nu\times\nu'),$$
--
--   where $\mathrm{KL}$ is the Kullback–Leibler divergence (7).
--
--   Fix $\varepsilon\ge0$ and a probability measure $\nu$ on $\mathsf Y$. Then:
--
--   1. **Lower semicontinuity.** If probability measures $\nu_n$ converge weakly to a probability measure $\nu'$ (that is, $\int\varphi\,d\nu_n\to\int\varphi\,d\nu'$ for every bounded continuous $\varphi:\mathsf Y\to\mathbb R$), then
--
--   $$K_\varepsilon(\nu,\nu')\le\liminf_{n\to\infty}K_\varepsilon(\nu,\nu_n).$$
--
--   2. **Convexity in the second argument.** For probability measures $\nu_1,\nu_2$ and $t\in[0,1]$,
--
--   $$K_\varepsilon\big(\nu,(1-t)\nu_1+t\nu_2\big)\le(1-t)K_\varepsilon(\nu,\nu_1)+tK_\varepsilon(\nu,\nu_2).$$
--
--   These are the two properties of $K_\varepsilon$ that the proof of Theorem 11 transfers from $K$: they drive the analogues of Theorem 8 (Jensen) and Theorem 9 (Fatou) for $\xi^{K_\varepsilon}$.
--
--   **Formalization Note** The shapes follow the published `OTSensitivity.Info.transportCost_lsc` and the two-point form of convexity; weights are `ENNReal.ofReal`.
--
--   Differences from the source:
--   - reading: "Kε(ν, ν′) is lower semicontinuous, and convex in its second argument" → sequential lower semicontinuity of $K_\varepsilon(\nu,\cdot)$ along weakly convergent sequences of probability measures, and two-point convexity in the second argument; reason: this is how the proof of Theorem 11 uses the claim (the Fatou step of Theorem 9 and the Jensen step of Theorem 8), and the same reading as the published lower semicontinuity of $K$
--   - generalization: $\varepsilon>0$ (the setting of Theorem 11) → every $\varepsilon\ge0$; reason: at $\varepsilon=0$ the claim is the corresponding property of $K$; the case $\varepsilon>0$ is an instance
--   - reading: the result names no cost assumption, or only "k continuous" → `IsCost k`: $k$ continuous into $[0,+\infty]$ and $k(y,y')=0\iff y=y'$; reason: this is the standing cost assumption of §3.1 (p. 9), under which every result of the section is stated
--   - generalization: the output space is a subset of $\mathbb R^{n_Y}$ (p. 4) → the output space $\mathsf Y$ is an arbitrary Polish space with its Borel σ-algebra; reason: closed subsets of Euclidean space are Polish, so the paper's setting is an instance; the same convention as the published base mission
--   - encoding: values of $k$, $K$, $K_\varepsilon$, KL in $[0,+\infty]$ → values in `ℝ≥0∞`; KL is Mathlib's `InformationTheory.klDiv`; reason: for probability measures `klDiv` is $+\infty$ off absolute continuity and $\int\log\frac{d\pi}{d\vartheta}\,d\pi$ otherwise, which is (7); same instances
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Theorem 11, p. 37

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting
import Definitions.Def_OTSensitivity_MaxFun_Supplement_Entropic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace OTSensitivity.MaxFun.Supplement

/-- Proof of Theorem 11, p. 37: `K_ε(ν, ·)` is lower semicontinuous under weak convergence of
probability measures (tested against every bounded continuous `φ`) and convex,
`K_ε(ν, (1 − t)ν₁ + tν₂) ≤ (1 − t)K_ε(ν, ν₁) + tK_ε(ν, ν₂)` for `t ∈ [0, 1]`, for every `ε ≥ 0`. -/
theorem lsc_convex {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴]
    [BorelSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k) (ε : ℝ≥0)
    (ν : Measure 𝒴) [IsProbabilityMeasure ν] :
    (∀ (νs : ℕ → Measure 𝒴) (ν' : Measure 𝒴), (∀ n, IsProbabilityMeasure (νs n)) →
        IsProbabilityMeasure ν' →
        (∀ φ : 𝒴 →ᵇ ℝ, Tendsto (fun n => ∫ y, φ y ∂(νs n)) atTop (𝓝 (∫ y, φ y ∂ν'))) →
        entropicTransportCost k ε ν ν' ≤ liminf (fun n => entropicTransportCost k ε ν (νs n)) atTop) ∧
      (∀ (ν₁ ν₂ : Measure 𝒴), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          entropicTransportCost k ε ν (ENNReal.ofReal (1 - t) • ν₁ + ENNReal.ofReal t • ν₂) ≤
            ENNReal.ofReal (1 - t) * entropicTransportCost k ε ν ν₁ +
              ENNReal.ofReal t * entropicTransportCost k ε ν ν₂) := by sorry

end OTSensitivity.MaxFun.Supplement
