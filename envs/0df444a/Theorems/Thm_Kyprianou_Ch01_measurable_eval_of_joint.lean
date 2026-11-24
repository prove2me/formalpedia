-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurable_eval_of_joint
-- name    : Kyprianou.Ch01.measurable_eval_of_joint
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T16:58:43.4332+00:00
-- url     : https://prove2.me/theorems/8ad8c2e4-e79c-4472-93f3-791d351639d9
-- title:
--   Joint product measurability yields measurable time-sections
-- statement:
--   If an integer-valued process $X$ is jointly measurable as a map $(\omega,t)\mapsto X_t(\omega)$ on $\Omega\times\mathbb{R}_{\ge 0}$, then for every fixed time $t$ the section $\omega\mapsto X_t(\omega)$ is measurable. This is the standard measurable-section consequence of product measurability, and is the first step in reducing first-passage measurability to countable rational clocks.
-- source:
--   Kyprianou (2006), Section 1.3.4; supporting lemma for measurability of firstNegativePassage. Standard measure-theory section fact.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurable_eval_of_joint
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    ∀ t : ℝ≥0, Measurable (X t) := by
  sorry
