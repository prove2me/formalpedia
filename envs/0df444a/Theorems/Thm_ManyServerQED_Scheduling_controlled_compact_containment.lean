-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_controlled_compact_containment
-- name    : ManyServerQED.Scheduling.controlled_compact_containment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:46:12.510873+00:00
-- url     : https://prove2.me/theorems/b19ca01d-2a5b-58b9-ba52-dc3666e9d3c8
-- title:
--   Compact containment of the diffusion-scaled queue state on each finite time interval
-- statement:
--   Let $X^n$ and $\Psi^n$ solve the controlled queue equations in the QED regime. Assume the diffusion-scaled initial state converges and each class queue satisfies
--   $$0\le X^n_i(t)-\Psi^n_i(t)\le\Bigl(\sum_j X^n_j(t)-n\Bigr)^+.$$
--   The upper bound follows from work conservation and also holds coordinatewise for the rounded-and-priority feedback in the proposed preemptive policy. For every $T\ge 0$ and $\eta>0$ there is a radius $B\ge 0$ such that for all sufficiently large $n$,
--   $$P\bigl(\exists t\in[0,T]:\|\widehat X^n(t)\|_\infty>B\bigr)<\eta.$$
--   The probability is the outer measure as defined by Lean's measure evaluation on sets. Centered primitive counts on deterministic clock horizons and a pathwise integral bound suffice for this estimate.
-- source:
--   Atar, Mandelbaum and Reiman (2004), https://arxiv.org/abs/math/0407058, Lemma 4(iii) pp. 33–34 and the use of tightness in (75), pp. 39–40. This auxiliary estimate isolates finite-horizon compact containment.

import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ManyServerQED.Scheduling

theorem controlled_compact_containment {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hc : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hq : ∀ n, 1 ≤ n → ∀ ω t i, 0 ≤ t →
      X n ω t i - Ψ n ω t i ≤ max ((∑ j, X n ω t j) - n) 0)
    (T : ℝ) (hT : 0 ≤ T) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      M.P {ω | ∃ t ∈ Set.Icc 0 T, B < ‖M.Xhat n (X n) ω t‖} < η := by sorry

end ManyServerQED.Scheduling
