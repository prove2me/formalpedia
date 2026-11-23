-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_Supplement_eq_69
-- name    : OTSensitivity.MaxFun.Supplement.eq_69
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:25:27.837219+00:00
-- url     : https://prove2.me/theorems/53f624ca-4ba2-4f75-b4fa-64c154f803f4
-- title:
--   (69) — on a Dirac target the entropic cost is the classical one: $K_\varepsilon(\nu,\delta_{y'})=K(\nu,\delta_{y'})=\int k(y,y')\,d\nu(y)$
-- statement:
--   Let $\mathsf Y$ be a Polish space with its Borel σ-algebra and let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be a cost that is continuous and vanishes exactly on the diagonal, $k(y,y')=0\iff y=y'$. For probability measures $\nu,\nu'$ on $\mathsf Y$, $\Pi(\nu,\nu')$ is the set of couplings, $K(\nu,\nu')=\inf_{\pi\in\Pi(\nu,\nu')}\int k\,d\pi$ is the optimal transport cost (1), and for $\varepsilon\ge0$ the **entropic OT functional** (8) is
--
--   $$K_\varepsilon(\nu,\nu')=\inf_{\pi\in\Pi(\nu,\nu')}\int\!\!\int k(y,y')\,d\pi(y,y')+\varepsilon\,\mathrm{KL}(\pi\,|\,\nu\times\nu'),$$
--
--   where $\mathrm{KL}$ is the Kullback–Leibler divergence (7).
--
--   Let $\nu$ be a probability measure on $\mathsf Y$, $y'\in\mathsf Y$ and $\varepsilon\ge0$. Then
--
--   $$K_\varepsilon(\nu,\delta_{y'})=K(\nu,\delta_{y'})=\int_{\mathsf Y}k(y,y')\,d\nu(y).$$
--
--   This identity opens the proof of Lemma 10 and, integrated, gives the upper bound in (27) of Theorem 11 and the equality case under functional dependence.
--
--   **Formalization Note** The two equalities are stated as a conjunction; $K$ is the published `RWPI.SqrtLasso.transportCost`.
--
--   Differences from the source:
--   - generalization: the output space is a subset of $\mathbb R^{n_Y}$ (p. 4) → the output space $\mathsf Y$ is an arbitrary Polish space with its Borel σ-algebra; reason: closed subsets of Euclidean space are Polish, so the paper's setting is an instance; the same convention as the published base mission
--   - encoding: values of $k$, $K$, $K_\varepsilon$, KL in $[0,+\infty]$ → values in `ℝ≥0∞`; KL is Mathlib's `InformationTheory.klDiv`; reason: for probability measures `klDiv` is $+\infty$ off absolute continuity and $\int\log\frac{d\pi}{d\vartheta}\,d\pi$ otherwise, which is (7); same instances
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Lemma 10, (69), p. 36

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting
import Definitions.Def_OTSensitivity_MaxFun_Supplement_Entropic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OTSensitivity.MaxFun.Supplement

/-- (69), p. 36: on a Dirac target the entropic cost is the classical one,
`K_ε(ν, δ_{y'}) = K(ν, δ_{y'}) = ∫ k(y, y') dν(y)`, for every `ε ≥ 0`. -/
theorem eq_69 {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k) (ε : ℝ≥0)
    (ν : Measure 𝒴) [IsProbabilityMeasure ν] (y' : 𝒴) :
    entropicTransportCost k ε ν (Measure.dirac y') =
        RWPI.SqrtLasso.transportCost k ν (Measure.dirac y') ∧
      RWPI.SqrtLasso.transportCost k ν (Measure.dirac y') = ∫⁻ y, k y y' ∂ν := by sorry

end OTSensitivity.MaxFun.Supplement
