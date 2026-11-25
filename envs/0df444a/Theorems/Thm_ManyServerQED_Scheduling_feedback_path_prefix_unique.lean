-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_feedback_path_prefix_unique
-- name    : ManyServerQED.Scheduling.feedback_path_prefix_unique
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:12:38.832381+00:00
-- url     : https://prove2.me/theorems/67f5c799-6dbf-54fb-94cd-931b40667d2a
-- title:
--   Pathwise causality and uniqueness of an existing queue under a state-feedback rule
-- statement:
--   Consider two existing paths of the same finite-$n$ queue from the same initial state, using the same time-homogeneous feedback rule $F$. Fix a time $T$. Suppose their class arrival histories agree up to $T$, their primitive service histories agree up to the service-clock values of the first path at $T$, and their primitive abandonment histories agree up to its abandonment-clock values at $T$. Then the two state paths agree throughout $[0,T]$. Taking the same primitive paths gives uniqueness whenever a controlled feedback path exists. The prefix formulation captures the causality used in the proof of admissibility.
-- source:
--   Atar, Mandelbaum and Reiman (2004), https://arxiv.org/abs/math/0407058, Proposition 1 and Appendix A.3, pp. 47–49, in particular the causality observation after (88).

import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory Filter Topology

namespace ManyServerQED.Scheduling

theorem feedback_path_prefix_unique {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ)
    (F : (Fin k → ℕ) → Fin k → ℝ) (X Y : Ω → ℝ → Fin k → ℕ)
    (hX : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t => F (X ω t)))
    (hY : M.IsControlled n X0 (fun ω t i => (Y ω t i : ℝ)) (fun ω t => F (Y ω t)))
    (ω ω' : Ω) (T : ℝ)
    (hA : ∀ i s, 0 ≤ s → s ≤ T → M.A n i ω s = M.A n i ω' s)
    (hR : ∀ i s, 0 ≤ s → s ≤ queueTime (fun ω t i => (X ω t i : ℝ))
        (fun ω t => F (X ω t)) ω i T → M.R n i ω s = M.R n i ω' s)
    (hS : ∀ i s, 0 ≤ s → s ≤ busyTime (fun ω t => F (X ω t)) ω i T →
      M.S n i ω s = M.S n i ω' s) :
    ∀ t ∈ Set.Icc 0 T, X ω t = Y ω' t := by sorry

end ManyServerQED.Scheduling
