-- Prove2me | Theorems.Thm_Kyprianou_Ch04_positiveRootSequenceWhLimit
-- name    : Kyprianou.Ch04.positiveRootSequenceWhLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:49:03.967359+00:00
-- url     : https://prove2.me/theorems/97070079-7328-5f9c-9762-50e9b1893f7d
-- title:
--   positiveRootSequenceWhLimit
-- statement:
--   Convex secants are increasing; choose maximal positive roots of each positive discount and apply the established secant and Wiener–Hopf quotient limits.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.positiveRootSequenceWhLimit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator : ¬ (∀ᵐ w : Ω ∂P, Antitone (fun t : NNReal => L.X t w)))
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hq0 : Tendsto q atTop (nhds 0))
    (beta : ℝ) (hpsi : L.ψ beta ≠ 0) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ (∀ n, L.ψ (r n) = q n) ∧
      Tendsto (fun n => (q n / r n) * ((r n-beta)/(q n-L.ψ beta))) atTop
        (nhds (max 0 (sInf ((fun theta : ℝ => L.ψ theta / theta) '' Ioi 0)) * beta / L.ψ beta)) := by
  sorry
