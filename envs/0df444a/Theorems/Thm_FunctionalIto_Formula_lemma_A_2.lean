-- Prove2me | Theorems.Thm_FunctionalIto_Formula_lemma_A_2
-- name    : FunctionalIto.Formula.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:23.584916+00:00
-- url     : https://prove2.me/theorems/42cd2531-de9c-4756-9ce9-edcd486e48df
-- title:
--   Lemma A.2, p. 22 — the first jump larger than α after an optional time is a stopping time (62)
-- statement:
--   Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space satisfying the usual hypotheses, let $V$ be an adapted process with cadlag paths taking values in a finite-dimensional normed space, let $\alpha\in\mathbb R$ and let $\sigma$ be an optional (stopping) time. Then
--   $$\tau=\inf\{t>\sigma:\ |V(t)-V(t-)|>\alpha\}\qquad(\inf\emptyset=+\infty)$$
--   is a stopping time.
--
--   The lemma makes the random partitions (31) and (66), which add the jump times of $A$ larger than $1/n$ to the dyadic grid, into sequences of stopping times.
--
--   **Formalization Note.** Stopping times take values in $[0,\infty]$ (`WithTop ℝ≥0`), with $\inf\emptyset=\infty$. "Optional time" is Dellacherie–Meyer's name for a stopping time and is encoded by Mathlib's `IsStoppingTime`. The usual hypotheses are the paper's standing assumption (§2) and are kept.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 22, Lemma A.2, (62)

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Formula_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace FunctionalIto.Formula

/-- Lemma A.2 (p. 22), (62): on a filtered probability space satisfying the usual
hypotheses, if `V` is an adapted cadlag process (with values in a finite-dimensional normed
space), `α ∈ ℝ` and `σ` is an optional (= stopping) time, then
`τ = inf {t > σ : ‖V(t) − V(t−)‖ > α}` (with `inf ∅ = ∞`) is a stopping time. -/
theorem lemma_A_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (hU : UsualHypotheses P ℱ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (α : ℝ) (V : ℝ≥0 → Ω → E) (hVadapt : Adapted ℱ V) (hVcadlag : ∀ ω, Cadlag (fun t => V t ω))
    (σ : Ω → WithTop ℝ≥0) (hσ : IsStoppingTime ℱ σ) :
    IsStoppingTime ℱ (fun ω => sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) ''
      {t : ℝ≥0 | σ ω < (t : WithTop ℝ≥0) ∧
        α < ‖V t ω - Function.leftLim (fun s => V s ω) t‖})) := by sorry

end FunctionalIto.Formula
