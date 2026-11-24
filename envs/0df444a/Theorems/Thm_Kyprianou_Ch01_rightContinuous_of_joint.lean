-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rightContinuous_of_joint
-- name    : Kyprianou.Ch01.rightContinuous_of_joint
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:29:58.145057+00:00
-- url     : https://prove2.me/theorems/4f3d6014-9a28-41f3-8769-179da419b83f
-- title:
--   Joint measurability yields pathwise right-continuity
-- statement:
--   Let $X:\mathbb{R}_{\ge 0}\times\Omega\to\mathbb{Z}$ be jointly measurable in calendar time and the sample point. The claim asserts that every path $t\mapsto X_t(\omega)$ is right-continuous on $\mathbb{R}_{\ge 0}$.
--
--   This is the missing bridge from the joint-measurability hypothesis of `firstNegativePassageMeasurable` to the Proved lemma `firstNegativePassageMeasurable_of_rightContinuous`. It is expected to be **false** (the same $\sqrt{2}$-spike that disproves `rightContinuous_of_sections` is jointly measurable).
-- source:
--   Kyprianou Fluctuations of Lévy Processes, Ch.1; bridge toward firstNegativePassageMeasurable (d9fd0249)

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rightContinuous_of_joint
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    ∀ ω : Ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t := by
  sorry
