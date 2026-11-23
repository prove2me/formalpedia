-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_Supplement_lemma_10
-- name    : OTSensitivity.MaxFun.Supplement.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:26:22.851994+00:00
-- url     : https://prove2.me/theorems/6e00abb6-b1e7-4113-8f78-f09140a4e861
-- title:
--   Lemma 10 (corrected: finite mixed-target cost) — strict convexity of the entropic cost between Dirac masses
-- statement:
--   Let $\mathsf Y$ be a Polish space with its Borel σ-algebra, and let $\nu$ be a probability measure on it. Let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be continuous, with $k(y,y')=0$ exactly when $y=y'$, and assume $\mathcal K(\nu\times\nu)=\int\!\int k\,d\nu\,d\nu<\infty$. Let $\varepsilon\ge0$, distinct $y_1,y_2\in\mathrm{supp}(\nu)$, and $0<t<1$. Write $\eta_t=(1-t)\delta_{y_1}+t\delta_{y_2}$, and let $K_\varepsilon$ be the entropic cost (8). The corrected strict-convexity assertion is
--
--   $$K_\varepsilon(\nu,\eta_t)<(1-t)K_\varepsilon(\nu,\delta_{y_1})+tK_\varepsilon(\nu,\delta_{y_2})
--   \quad\Longleftrightarrow\quad K_\varepsilon(\nu,\eta_t)<\infty.$$
--
--   Thus (26) holds on exactly the finite mixed-cost domain, including instances with infinite individual Dirac costs. As printed, Lemma 10 also permits both sides of (26) to be infinite; the inverse-distance example described below refutes that unrestricted assertion. This is the support used for max-functionality in Theorem 11.
--
--   **Formalization Note** Costs and integrals take values in `ℝ≥0∞`. The weights are `ENNReal.ofReal (1 - t)` and `ENNReal.ofReal t`; $\mathcal K(\nu\times\nu)$ is the published `OTSensitivity.MaxFun.MK`, and support is `Measure.support`. The classical $K$ is the published `RWPI.SqrtLasso.transportCost`. No conditional kernel occurs in this item.
--
--   Differences from the source:
--   - correction: (26) for every $y_1\ne y_2$ in $\mathrm{supp}(\nu)$ and $t\in(0,1)$, under $\mathcal K(\nu\times\nu)<\infty$ only → the strict inequality holds if and only if $K_\varepsilon(\nu,(1-t)\delta_{y_1}+t\delta_{y_2})<\infty$, without finiteness assumptions on the individual Dirac costs; reason: the printed claim can read $\infty<\infty$; a source-admissible example is uniform ν on [0,1] with integrable two-dimensional inverse-distance singularities at (1/2,0) and (1/2,1); every binary-target coupling then has infinite cost. The proof on pp. 36–37 establishes strictness when the right side is finite. If the mixed-target cost is finite and the right side infinite, strictness is immediate. If the mixed-target cost is infinite, no strict upper bound exists. This retains every instance where (26) is true and removes the earlier draft's unnecessary finite-Dirac restrictions
--   - reading: the result names no cost assumption, or only "k continuous" → `IsCost k`: $k$ continuous into $[0,+\infty]$ and $k(y,y')=0\iff y=y'$; reason: the statement names only "k continuous"; zero exactly on the diagonal is the standing assumption of §3.1 (p. 9) and the proof uses it (p. 37, "0 = k(y1, y1) + k(y2, y2)"); without it (26) fails for $k\equiv0$
--   - generalization: the output space is a subset of $\mathbb R^{n_Y}$ (p. 4) → the output space $\mathsf Y$ is an arbitrary Polish space with its Borel σ-algebra; reason: closed subsets of Euclidean space are Polish, so the paper's setting is an instance; the same convention as the published base mission
--   - encoding: values of $k$, $K$, $K_\varepsilon$, KL in $[0,+\infty]$ → values in `ℝ≥0∞`; KL is Mathlib's `InformationTheory.klDiv`; reason: for probability measures `klDiv` is $+\infty$ off absolute continuity and $\int\log\frac{d\pi}{d\vartheta}\,d\pi$ otherwise, which is (7); same instances
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Lemma 10, (26), p. 11; proof on pp. 36–37

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting
import Definitions.Def_OTSensitivity_MaxFun_Supplement_Entropic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OTSensitivity.MaxFun.Supplement

/-- Lemma 10, p. 11: strict convexity (26) of `K_ε(ν, ·)` between Dirac masses at two distinct
points of `supp ν`, for every `ε ≥ 0`, when `𝒦(ν × ν) < ∞`. Disclosed correction: the
strict inequality holds exactly when the mixed-target cost is finite. If the right side is
finite this is the case treated by the proof (p. 36); if only the mixed-target cost is finite
the inequality is immediate. An infinite mixed-target cost makes both sides `+∞`. -/
theorem lemma_10 {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴]
    [BorelSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k) (ε : ℝ≥0)
    (ν : Measure 𝒴) [IsProbabilityMeasure ν] (hν : OTSensitivity.MaxFun.MK k ν < ⊤)
    (y₁ y₂ : 𝒴) (hy₁ : y₁ ∈ ν.support) (hy₂ : y₂ ∈ ν.support) (hne : y₁ ≠ y₂)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (entropicTransportCost k ε ν
        (ENNReal.ofReal (1 - t) • Measure.dirac y₁ + ENNReal.ofReal t • Measure.dirac y₂) <
      ENNReal.ofReal (1 - t) * entropicTransportCost k ε ν (Measure.dirac y₁) +
        ENNReal.ofReal t * entropicTransportCost k ε ν (Measure.dirac y₂)) ↔
      entropicTransportCost k ε ν
        (ENNReal.ofReal (1 - t) • Measure.dirac y₁ + ENNReal.ofReal t • Measure.dirac y₂) < ⊤ := by sorry

end OTSensitivity.MaxFun.Supplement
