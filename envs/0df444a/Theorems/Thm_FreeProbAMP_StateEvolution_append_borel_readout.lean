-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_append_borel_readout
-- name    : FreeProbAMP.StateEvolution.append_borel_readout
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:50.121536+00:00
-- url     : https://prove2.me/theorems/1bc886f4-99eb-43db-9a0f-05509fa2b37a
-- title:
--   Lemma 7.1 — append a null-discontinuity Borel readout
-- statement:
--   Suppose $(X_i^d)_{i\le n(d)}\subset\mathbb R^q$ converges empirically to an all-moment vector $X$, where $n(d)>0$ and $n(d)\to\infty$. Let $f:\mathbb R^q\to\mathbb R$ be bounded and Borel with $\mathbb P(X\in\operatorname{Disc}(f))=0$. Then
--
--   $$(X_i^d,f(X_i^d))_{i\le n(d)}\xrightarrow{\rm emp}(X,f(X)).$$
--
--   For every bounded continuous $f_a:\mathbb R^q\to\mathbb R$,
--
--   $$\frac1{n(d)}\sum_i|f_a(X_i^d)-f(X_i^d)|^2\xrightarrow{\mathbb P}\mathbb E|f_a(X)-f(X)|^2.$$
--
--   This extends empirical convergence to the permitted discontinuous terminal readout and also controls its approximation error. Both assertions retain the full bounded Borel, null-discontinuity scope.
--
--   Differences from the source:
--   - encoding: sample sizes n(d) with n(d) → ∞ → n(d) ≥ 1 for every d; reason: nondegeneracy only; at n = 0 the source's 1/n and n^{-1/2} normalizations are undefined, and n(d) → ∞ leaves only finitely many such d, which no limit statement sees
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), pp. 36–37, Lemma 7.1

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Lemma 7.1, submission pp.36–37, both conclusions. -/
theorem append_borel_readout
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ → ℕ) (q : ℕ) (hn : ∀ d, 0 < n d)
    (X : (d : ℕ) → Ω → Fin (n d) → Fin q → ℝ) (Y : E → Fin q → ℝ)
    (he : Empirical μ ν n X Y) (f : (Fin q → ℝ) → ℝ) (hf : BoundedReadout ν Y f) :
    Empirical μ ν n (fun d ω i => append (X d ω i) (f (X d ω i)))
      (fun ξ => append (Y ξ) (f (Y ξ))) ∧
    ∀ fa : (Fin q → ℝ) → ℝ, Continuous fa → (∃ C : ℝ, ∀ x, |fa x| ≤ C) →
      InProb μ (fun d ω => avg (n d) (fun i => |fa (X d ω i)-f (X d ω i)|^2))
        (∫ ξ, |fa (Y ξ)-f (Y ξ)|^2 ∂ν) := by sorry

end FreeProbAMP.StateEvolution
