-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_lemma_4
-- name    : OTSensitivity.MaxFun.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:25.641269+00:00
-- url     : https://prove2.me/theorems/c8225541-cfd2-4b92-b5f0-bf3660711c5c
-- title:
--   Lemma 4 — K(ν, ·) is strictly convex between Dirac masses at points of supp ν
-- statement:
--   Let $\mathsf Y$ be a Polish space and $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ continuous with $k(y,y')=0\iff y=y'$. Let $\nu$ be a probability measure on $\mathsf Y$ with $\mathcal K(\nu\times\nu)=\iint k\,d\nu\,d\nu<+\infty$. Let $y_1\ne y_2$ be two points of the support $\operatorname{supp}(\nu)$ such that $K(\nu,\delta_{y_1})<+\infty$ and $K(\nu,\delta_{y_2})<+\infty$. Then for every $t\in(0,1)$
--
--   $$K\big(\nu,(1-t)\delta_{y_1}+t\delta_{y_2}\big)<(1-t)K(\nu,\delta_{y_1})+tK(\nu,\delta_{y_2}).\tag{19}$$
--
--   The map $K(\nu,\cdot)$ is convex; the lemma says it is strictly convex along segments joining two distinct Dirac masses in the support of $\nu$. This is what forces the conditional laws to be Dirac masses in the equality case of Theorem 5.
--
--   **Disclosed correction.** The printed lemma does not assume $K(\nu,\delta_{y_1}),K(\nu,\delta_{y_2})<+\infty$, and its proof treats exactly that case ((55), p. 33). The assumption $\mathcal K(\nu\times\nu)<\infty$ makes $K(\nu,\delta_y)=\int k(\cdot,y)\,d\nu$ finite only for $\nu$-almost every $y$, not for every $y$ in the support, and there are admissible costs with $\mathcal K(\nu\times\nu)<\infty$ for which both sides of (19) equal $+\infty$. Theorem 5 is unaffected: its proof applies the lemma only where these quantities are finite. The condition $k(y,y')=0\iff y=y'$ is the standing assumption of §3.1 (p. 9), which the proof uses in (56).
--
--   **Formalization Note** $K$ is the published `RWPI.SqrtLasso.transportCost`; values lie in $[0,+\infty]$ and the weights are `ENNReal.ofReal (1 - t)`, `ENNReal.ofReal t`, so the mixture is a probability measure. The support is Mathlib's `Measure.support`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Lemma 4 and (19), p. 10; proof (55)–(56), p. 33; standing assumption of §3.1, p. 9

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- Lemma 4, p. 10: strict convexity of `K(ν, ·)` between Dirac masses at two distinct points of
`supp ν`, (19). Disclosed correction: the finiteness of `K(ν, δ_{y₁})` and `K(ν, δ_{y₂})` is
added (the case treated by the proof, (55), p. 33); without it both sides of (19) can be `+∞`. -/
theorem lemma_4 {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (ν : Measure 𝒴) [IsProbabilityMeasure ν] (hν : MK k ν < ⊤)
    (y₁ y₂ : 𝒴) (hy₁ : y₁ ∈ ν.support) (hy₂ : y₂ ∈ ν.support) (hne : y₁ ≠ y₂)
    (hfin₁ : RWPI.SqrtLasso.transportCost k ν (Measure.dirac y₁) < ⊤)
    (hfin₂ : RWPI.SqrtLasso.transportCost k ν (Measure.dirac y₂) < ⊤)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    RWPI.SqrtLasso.transportCost k ν
        (ENNReal.ofReal (1 - t) • Measure.dirac y₁ + ENNReal.ofReal t • Measure.dirac y₂) <
      ENNReal.ofReal (1 - t) * RWPI.SqrtLasso.transportCost k ν (Measure.dirac y₁) +
        ENNReal.ofReal t * RWPI.SqrtLasso.transportCost k ν (Measure.dirac y₂) := by sorry

end OTSensitivity.MaxFun
