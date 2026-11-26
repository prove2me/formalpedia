-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
-- name    : ManyServerQED.Scheduling.queue_hjb_row_integral_paths
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:24:58.225092+00:00
-- url     : https://prove2.me/theorems/0f76d878-2ec0-5f1f-833f-180bd2299828
-- title:
--   Local integrability and Lipschitz bounds for queue HJB accumulators
-- statement:
--   In each controlled work-conserving row the drift, discounted cost and discounted HJB gap admit continuous time primitives, with the last two nondecreasing. A common compact state bound implies a uniform Lipschitz bound for the three primitives over the given horizon. The discounted cost is the nonnegative integral of its integrand.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_controlled_queue_state_and_effective_noise_are_cadlag
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_integrands_on_bounded_state_sets
import Theorems.Thm_ManyServerQED_Scheduling_queue_state_and_allocation_jointly_measurable_in_past
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_row_integral_paths {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (γ ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (hC : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n)) :
    let z (n : ℕ) (ω : Ω) := M.Xhat n (X n) ω
    let u (n : ℕ) (ω : Ω) := uProc n u0 (X n) (Ψ n) ω
    let b (n : ℕ) (ω : Ω) (t : ℝ) := drift M.diffData (z n ω t) (u n ω t)
    let c (n : ℕ) (ω : Ω) (t : ℝ) := Real.exp (-γ*t) * costOfTilde Lt (z n ω t) (u n ω t)
    let g (n : ℕ) (ω : Ω) (t : ℝ) :=
      Real.exp (-γ*t)*((∑ i, b n ω t i*grad f (z n ω t) i)+costOfTilde Lt (z n ω t) (u n ω t)-
        hamiltonian M.diffData (costOfTilde Lt) (z n ω t) (grad f (z n ω t)))
    let B (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) := ∫ s in (0:ℝ)..t, b n ω s i
    let C (n : ℕ) (ω : Ω) (t : ℝ) := ∫ s in (0:ℝ)..t, c n ω s
    let G (n : ℕ) (ω : Ω) (t : ℝ) := ∫ s in (0:ℝ)..t, g n ω s
    (∀ n, 1 ≤ n → ∀ ω,
      (∀ i, ContinuousOn (fun t => B n ω t i) (Ici 0)) ∧
      ContinuousOn (C n ω) (Ici 0) ∧ ContinuousOn (G n ω) (Ici 0) ∧
      MonotoneOn (C n ω) (Ici 0) ∧ MonotoneOn (G n ω) (Ici 0) ∧
      (∀ T : ℝ, 0 ≤ T → ENNReal.ofReal (C n ω T) =
        ∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal (c n ω t) ∂volume) ∧
      (∀ T : ℝ, 0 ≤ T →
        (∀ i, IntervalIntegrable (fun t => b n ω t i) volume 0 T) ∧
        IntervalIntegrable (c n ω) volume 0 T ∧ IntervalIntegrable (g n ω) volume 0 T) ∧
      (∀ t : ℝ, 0 ≤ t → u n ω t ∈ stdSimplex ℝ (Fin k))) ∧
    (∀ T A : ℝ, ∃ a > 0, ∀ n, 1 ≤ n → ∀ ω,
      (∀ t ∈ Icc (0:ℝ) T, ‖z n ω t‖ ≤ A) →
      ∀ s ∈ Icc (0:ℝ) T, ∀ t ∈ Icc (0:ℝ) T,
        (∀ i, |B n ω s i-B n ω t i| ≤ a*|s-t|) ∧
        |C n ω s-C n ω t| ≤ a*|s-t| ∧ |G n ω s-G n ω t| ≤ a*|s-t|) := by sorry
