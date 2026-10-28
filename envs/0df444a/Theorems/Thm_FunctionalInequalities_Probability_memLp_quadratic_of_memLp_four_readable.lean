-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_memLp_quadratic_of_memLp_four_readable
-- name    : FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:03.464778+00:00
-- url     : https://prove2.me/theorems/80afcd22-0f06-48b5-88c9-0fb875897eef
-- title:
--   Quadratic Forms Preserve $L^4$ Integrability at Exponent $2$
-- statement:
--   This is a general moment-transfer lemma for quadratic forms.
--
--   Let $(\alpha,\mu)$ be a measurable space with a measure, let $E$ be a real inner-product normed group, let $f:\alpha\to E$ satisfy `MemLp f 4 μ`, and let $A:E\to E$ be a continuous linear map. Then the scalar quadratic form $x\mapsto\langle A(f(x)),f(x)\rangle$ belongs to `MemLp` with exponent $2$:
--
--   $$x\longmapsto\langle A(f(x)),f(x)\rangle\in L^2(\mu).$$
--
--   The lemma is a reusable integrability fact for quadratic observables, with no probability, finite-dimensionality, or measurability assumption on $f$ beyond the stated `MemLp` hypothesis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 300000 in
--   theorem memLp_quadratic_of_memLp_four {alpha E : Type*} [MeasurableSpace alpha]
--       [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mu : Measure alpha}
--       {f : alpha → E} (hf : MemLp f 4 mu) (A : E →L[ℝ] E) :
--       MemLp (fun x => ⟪A (f x), f x⟫) 2 mu
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Moments`](https://prove2.me/theorems/b17c0176-d838-4b45-bc76-c9e62313e1ce).
--
--   Previous: [`sum_variance_entries_eq_integral_trace_sub_trace_mean`](https://prove2.me/theorems/88527e56-76ae-4a12-8518-4edc0d238008).
--
--   [Source excerpt, lines 509–513](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Moments.lean#L509-L513) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Moments.lean#L509-L531 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Moments`, declaration `FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments

open MeasureTheory
open scoped RealInnerProductSpace
set_option maxHeartbeats 300000

theorem FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four_readable {alpha E : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mu : Measure alpha}
    {f : alpha → E} (hf : MemLp f 4 mu) (A : E →L[ℝ] E) :
    MemLp (fun x => ⟪A (f x), f x⟫) 2 mu := by sorry
