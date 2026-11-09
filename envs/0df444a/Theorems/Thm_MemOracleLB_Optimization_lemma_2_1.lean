-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_2_1
-- name    : MemOracleLB.Optimization.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:11.257904+00:00
-- url     : https://prove2.me/theorems/d8927547-50ee-4e26-b72d-a7fe7f6c3a5c
-- title:
--   Lemma 2.1 — Relative-entropy toolbox (a)–(e)
-- statement:
--   For probability measures $\mu,\nu$ on a measurable space, all five entropy properties hold, including when the divergence is infinite:
--
--   1. $D_{\rm KL}(\mu\|\nu)\ge0$ (when $\mu\ll\nu$ and $\log\frac{d\mu}{d\nu}$ is $\mu$-integrable, $\int\log\frac{d\mu}{d\nu}\,d\mu\ge0$; otherwise the divergence is $+\infty$), and
--      $$D_{\rm KL}(\mu\|\nu)=\sup_{g\text{ bounded measurable}}\left\{\int g\,d\mu-\log\int e^g\,d\nu\right\}.$$
--   2. Every measurable $T$ satisfies $D_{\rm KL}(T_\#\mu\|T_\#\nu)\le D_{\rm KL}(\mu\|\nu)$.
--   3. For any finite family of pairs of probability measures, possibly on different measurable spaces,
--      $$D_{\rm KL}\!\left(\bigotimes_i\mu_i\middle\|\bigotimes_i\nu_i\right)=\sum_iD_{\rm KL}(\mu_i\|\nu_i).$$
--   4. If $F$ is measurable and $\nu(F)>0$, then $D_{\rm KL}(\nu(\cdot\mid F)\|\nu)=\log(1/\nu(F))$.
--   5. With $\|\mu-\nu\|_{\rm TV}=\sup_{F\text{ measurable}}|\mu(F)-\nu(F)|$,
--      $$\|\mu-\nu\|_{\rm TV}\le\sqrt{D_{\rm KL}(\mu\|\nu)/2}.$$
--
--   These are the entropy comparison tools used throughout the Gaussian arguments. The empty finite product is included and gives divergence zero.
--
--   Differences from the source:
--   - encoding: nonnegative relative entropy and a possibly unbounded variational supremum → nonnegativity of the log-likelihood integral whenever mu << nu and llr is integrable, klDiv in [0,infinity], a supremum in EReal, and a nonnegative extended-real square root; reason: klDiv is ofReal of that integral (infinite otherwise), so nonnegativity is stated where it has content; infinite divergence remains infinite, and no real-valued unbounded-supremum default is used
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 2.1, PDF p. 8 (printed p. 7), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Probability

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
universe u21 v21

namespace MemOracleLB.Optimization

/-- Lemma 2.1(a)–(e), PDF p.8 (printed p.7). All five clauses, including infinite entropy.
Nonnegativity is stated for the real log-likelihood integral: `klDiv` is `ofReal` of it,
so `0 ≤ klDiv μ ν` alone would be automatic. -/
theorem lemma_2_1 :
    (∀ {α : Type u21} [MeasurableSpace α] (μ ν : Measure α)
      [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      (μ ≪ ν → Integrable (llr μ ν) μ → 0 ≤ ∫ x, llr μ ν x ∂μ) ∧
      (klDiv μ ν).toEReal =
        ⨆ g : {g : α → ℝ // Measurable g ∧ ∃ M : ℝ, ∀ x, |g x| ≤ M},
          (((∫ x, g.val x ∂μ) - Real.log (∫ x, Real.exp (g.val x) ∂ν) : ℝ) : EReal)) ∧
    (∀ {α : Type u21} {β : Type v21} [MeasurableSpace α] [MeasurableSpace β]
      (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (T : α → β), Measurable T → klDiv (μ.map T) (ν.map T) ≤ klDiv μ ν) ∧
    (∀ {ι : Type u21} [Fintype ι] {α : ι → Type v21} [∀ i, MeasurableSpace (α i)]
      (μ ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
      [∀ i, IsProbabilityMeasure (ν i)],
      klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i)) ∧
    (∀ {α : Type u21} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
      (F : Set α), MeasurableSet F → 0 < ν F →
      klDiv (cond ν F) ν = ENNReal.ofReal (Real.log (1 / ν.real F))) ∧
    (∀ {α : Type u21} [MeasurableSpace α] (μ ν : Measure α)
      [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      totalVariation μ ν ≤ (klDiv μ ν / 2) ^ (1 / 2 : ℝ)) := by sorry

end MemOracleLB.Optimization
