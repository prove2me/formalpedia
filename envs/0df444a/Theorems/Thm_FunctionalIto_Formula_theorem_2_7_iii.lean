-- Prove2me | Theorems.Thm_FunctionalIto_Formula_theorem_2_7_iii
-- name    : FunctionalIto.Formula.theorem_2_7_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:27.190631+00:00
-- url     : https://prove2.me/theorems/97c32981-57fb-4d95-b9c5-82512c757f80
-- title:
--   Theorem 2.7 (iii), p. 7 — Z(t) = F_t(X_t, A_t) is predictable for F ∈ ℂ_l^{0,0} verifying (10)
-- statement:
--   In the setting of §2 ($X$ a continuous semimartingale and $A$ the cadlag density of its quadratic variation, on a filtered probability space satisfying the usual hypotheses), let $F$ be a nonanticipative functional in $\mathbb C^{0,0}_l([0,T))$ that verifies (10). Then the process
--   $$Z(t)=F_t(X_t,A_t),\qquad t\in[0,T),$$
--   is predictable.
--
--   Predictability of $F_t(X_t,A_t)$, applied to the derivatives of $F$, is what makes the integrands of the functional Itô formula admissible stochastic integrands.
--
--   **Formalization Note.** $Z$ is extended by $0$ for $t\ge T$, and predictability is measurability with respect to Mathlib's predictable $\sigma$-algebra on $[0,\infty)\times\Omega$. Only the alternative "$F$ verifies (10)" of the hypothesis "$A$ is continuous or $F$ verifies (10)" is formalized. $F$ is assumed $\mathcal B_t$-measurable (Definition 2.1, part of "nonanticipative functional"); without it the statement is false: a $d_\infty$-Lipschitz functional of the jump time of $A$ built from a non-measurable set of times lies in $\mathbb C^{0,0}_l$ but yields a non-measurable $Z$.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, pp. 6–7, Theorem 2.7 (iii); proof p. 23

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Formula_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace FunctionalIto.Formula

/-- Theorem 2.7 (iii) (p. 7): if `F ∈ ℂ_l^{0,0}([0,T))` verifies (10), then the process
`Z(t) = F_t(X_t, A_t)`, `t ∈ [0,T)`, is predictable. The process is extended by `0` for
`t ≥ T`; the statement is measurability with respect to the predictable σ-algebra on
`ℝ≥0 × Ω`. -/
theorem theorem_2_7_iii {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hU : UsualHypotheses P ℱ) (X V M : ℝ≥0 → Ω → Fin d → ℝ)
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (hS : IsContSemimartingale P ℱ X V M A)
    (T : ℝ≥0) (F : Functional d ℝ) (hFna : IsNonanticipative F)
    (hFm : IsCanonicallyMeasurable T F) (hF : LeftContinuous T F) (h10 : PredictableInV T F) :
    Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      if p.1 < T then F p.1 (fun s => X s p.2) (fun s => A s p.2) else 0) := by sorry

end FunctionalIto.Formula
