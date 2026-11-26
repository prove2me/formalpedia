-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_coupled_lipschitz_observable_compact_suprema_converge
-- name    : ManyServerQED.Scheduling.coupled_lipschitz_observable_compact_suprema_converge
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:19:46.3918+00:00
-- url     : https://prove2.me/theorems/57a2e968-cd86-5388-84a2-883cd95781c5
-- title:
--   Compact suprema converge under a locally uniform coupling
-- statement:
--   On a locally uniform queue path coupling, the supremum of a nonnegative Lipschitz observable over a compact interval converges almost surely to the corresponding limit supremum.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.coupled_lipschitz_observable_compact_suprema_converge {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (T : ℝ≥0)
    (v : (Fin (k+k+k+2) → ℝ) → ℝ) (hv : Continuous v)
    (hn : ∀ z, 0 ≤ v z)
    (h : ∀ x y, |v x-v y| ≤ ∑ i, |x i-y i|) :
    let S (ω : d.Ω') := ⨆ t : Icc (0:ℝ) T, ENNReal.ofReal (v (d.limit ω t.1))
    let R (n : ℕ) (ω : d.Ω') := ⨆ t : Icc (0:ℝ) T, ENNReal.ofReal (v (d.row n ω t.1))
    (∀ ω, S ω ≠ ⊤) ∧
    ∀ᵐ ω ∂d.Q, Tendsto (fun n => R n ω) atTop (𝓝 (S ω)) := by sorry
