-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_5_3
-- name    : OnlineRealSampling.Exact.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:14:50.82467+00:00
-- url     : https://prove2.me/theorems/faebc296-368b-4465-b745-baecc718e44e
-- title:
--   Proposition 5.3 — IntervalSample samples exactly
-- statement:
--   Let $F$ have a valid oracle and $M\ge1$, and let $Z$ be uniform on $\{0,\dots,M-1\}$, independent of the fair bits. Then:
--   1. almost surely, IntervalSample$(F,(Z,M))$ halts and its output $X$ is the unique index with $Q\in[F(X-1),F(X)]$;
--   2. $\Pr(X=x)=f(x)$ for every $x$;
--   3. for every $x$ with $f(x)>0$, conditionally on $X=x$, $Q$ is uniform on $[F(x-1),F(x)]$: for every Borel set $A$,
--   $$\Pr(X=x,\ Q\in A)=\lambda\big(A\cap[F(x-1),F(x)]\big).$$
--
--   This is the exactness of a single step, and the conditional uniformity of $Q$ is the randomness that Recycle reuses.
--
--   Differences from the source:
--   - encoding: aside from the probability-zero event that Q equals a CDF boundary → almost surely (termination included); reason: the same statement up to a null event
--   - encoding: Q uniform on [F(x−1),F(x)] conditionally on X = x → Pr(X = x, Q ∈ A) = Lebesgue measure of A ∩ [F(x−1),F(x)] for all Borel A; reason: equivalent, since Pr(X = x) = f(x) is the length of the interval
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 5.3, PDF 11 / printed 10

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 5.3 (exactness of IntervalSample). With `Z ∼ Unif{0,…,M-1}` independent of the
fair bits: almost surely IntervalSample halts and its output `X` is the unique index with
`Q ∈ [F(X-1), F(X)]`; `X` has law `F`; and, conditionally on `X = x` for any `x` with `f(x) > 0`,
`Q` is uniform on `[F(x-1), F(x)]`. -/
theorem proposition_5_3 (w : ℕ) (O : CDFOracle) (hO : O.Valid) (M : ℕ) (hM : 1 ≤ M) :
    (∀ᵐ p ∂(stepMeasure M), ∃ c : Config ISState,
        intervalSampleOn w O.toOracleAccess M p = some c ∧
        cdfPrev O.F c.st.lo ≤ Qvar M p.1 p.2 ∧ Qvar M p.1 p.2 ≤ O.F c.st.lo ∧
        ∀ y : ℕ, cdfPrev O.F y ≤ Qvar M p.1 p.2 → Qvar M p.1 p.2 ≤ O.F y → y = c.st.lo) ∧
      (∀ x : ℕ, stepMeasure M (isEvent w O.toOracleAccess M x) = ENNReal.ofReal (pmf O.F x)) ∧
      (∀ x : ℕ, 0 < pmf O.F x → ∀ A : Set ℝ, MeasurableSet A →
        stepMeasure M {p | p ∈ isEvent w O.toOracleAccess M x ∧ Qvar M p.1 p.2 ∈ A} =
          volume (A ∩ Set.Icc (cdfPrev O.F x) (O.F x))) := by sorry

end OnlineRealSampling.Exact
