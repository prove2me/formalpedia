-- Prove2me | Theorems.Thm_HighDimStat_UniformLaws_uniform_law_rademacher_complexity
-- name    : HighDimStat.UniformLaws.uniform_law_rademacher_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:43.510976+00:00
-- url     : https://prove2.me/theorems/9bcc49aa-f93d-42d4-9479-8b352a5aa456
-- title:
--   Theorem 4.10 -- a uniform law via Rademacher complexity
-- statement:
--   **Theorem 4.10 (a uniform law via Rademacher complexity).** For any $b$-uniformly bounded
--   class of functions $F$, any positive integer $n\ge1$, and any scalar $\delta\ge0$,
--
--   $$
--   \|\mathbb P_n-P\|_F \;\le\; 2R_n(F)+\delta
--   $$
--
--   with $P$-probability at least $1-\exp(-n\delta^2/2b^2)$.
--
--   This is the chapter's central non-asymptotic uniform law: it converts a purely deterministic
--   complexity measure of the function class $F$ (the Rademacher complexity $R_n(F)$) into a
--   high-probability bound on the worst-case deviation of the empirical average from the
--   population average, uniformly over $F$ — the source, via specific choices of $F$, of both
--   the classical Glivenko–Cantelli theorem (Theorem 4.4) and the uniform convergence guarantees
--   underlying empirical risk minimization.
--
--   **Formalization Note** The book's further "consequently... a.s.→0" qualitative corollary
--   (obtained via Borel–Cantelli once $R_n(F)=o(1)$) is not included in this goal's conclusion:
--   it is a statement about an infinite sequence of samples and asymptotic convergence, a
--   genuinely different (and more elaborate) formal object than the single-$n$ non-asymptotic
--   tail bound (4.14) itself, and is left as natural follow-on work (see `description.md`). The
--   Rademacher sequence $\varepsilon$ and the samples $X$ are packaged into one jointly
--   independent family `Z : ℕ → Ω → D × ℝ` with `Z i = (Xᵢ,εᵢ)`, plus an explicit hypothesis that
--   `Xᵢ` and `εᵢ` are themselves independent of one another at each index `i` — jointly capturing
--   "$\varepsilon$ independent of $X$, both i.i.d." exactly.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 105 (PDF p. 125), Theorem 4.10, Eq. (4.14)

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_empProcessDeviation
import Definitions.Def_HighDimStat_UniformLaws_rademacherComplexity
import Definitions.Def_HighDimStat_UniformLaws_IsUniformlyBounded
import Definitions.Def_HighDimStat_UniformLaws_IsRademacherVariable

open MeasureTheory ProbabilityTheory

namespace HighDimStat.UniformLaws

/-- **Theorem 4.10** (a uniform law via Rademacher complexity), Wainwright, *High-Dimensional
Statistics* (2019), p. 105. For any `b`-uniformly bounded class of functions `F`, any positive
integer `n≥1`, and any scalar `δ≥0`, `‖Pₙ-P‖_F ≤ 2Rₙ(F)+δ` with `P`-probability at least
`1-exp(-nδ²/2b²)`. A hypothesis `hf` that each `f j` is measurable guards the empirical-process
and Rademacher-complexity integrals against Mathlib's junk value on a non-integrable/
non-measurable function. -/
theorem uniform_law_rademacher_complexity {D ι Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (f : ι → D → ℝ) (hf : ∀ j, Measurable (f j))
    (b : ℝ) (hb : IsUniformlyBounded f b)
    (Z : ℕ → Ω → D × ℝ) (X0 : Ω → D)
    (hIndepZ : iIndepFun Z Prob)
    (hXIdent : ∀ i, IdentDistrib (fun ω => (Z i ω).1) X0 Prob Prob)
    (hEpsRad : ∀ i, IsRademacherVariable (fun ω => (Z i ω).2) Prob)
    (hXEpsIndep : ∀ i, IndepFun (fun ω => (Z i ω).1) (fun ω => (Z i ω).2) Prob)
    (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 ≤ δ) :
    Prob.real {ω | empProcessDeviation f (fun i ω => (Z i ω).1) X0 Prob n ω ≤
      2 * rademacherComplexity f (fun i ω => (Z i ω).1) (fun i ω => (Z i ω).2) Prob n + δ} ≥
      1 - Real.exp (-((n : ℝ) * δ ^ 2) / (2 * b ^ 2)) := by sorry

end HighDimStat.UniformLaws
