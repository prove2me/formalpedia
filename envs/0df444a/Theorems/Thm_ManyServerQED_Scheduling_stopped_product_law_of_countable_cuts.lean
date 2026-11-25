-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_stopped_product_law_of_countable_cuts
-- name    : ManyServerQED.Scheduling.stopped_product_law_of_countable_cuts
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:58:44.228024+00:00
-- url     : https://prove2.me/theorems/5c601e89-36f6-5c49-99e1-b0ffd35aab39
-- title:
--   Joint product law under countable cut approximation
-- statement:
--   Let $P$ be a finite measure, $A$ an event under consideration, and $J$ a countable partially ordered set of cuts. At resolution $n$, the actual cut is $K_n$, and the deterministic cut $j$ has information $\mathcal G_{n,j}$ and real-valued output vector $F_{n,j}$. Assume the information grows with $j$, $A\cap\{K_n\le j\}$ belongs to $\mathcal G_{n,j}$, and the lower events $\{K_n\le j\}$ are measurable. Assume that every deterministic-cut output is independent of its information and has the same law $Q$. If each coordinate of the chosen output $F_{n,K_n}$ is eventually equal to the corresponding coordinate of $g$ on every sample, then $g$ is measurable and
--   $$g_*(P|_A)=P(A)Q.$$
--   The output vector may have an arbitrary index set with its product sigma algebra. This gives the path-space product law for right-continuous integer counting paths sampled at rounded operational clocks.
-- source:
--   Auxiliary path-space version of the grid conditioning and right-limit argument in Atar, Mandelbaum and Reiman, https://arxiv.org/pdf/math/0407058#page=49, Appendix A.3

import Mathlib
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped ENNReal

theorem ManyServerQED.Scheduling.stopped_product_law_of_countable_cuts {Ω I J : Type*} [m : MeasurableSpace Ω] [Countable J]
    [PartialOrder J] [MeasurableSpace J] [DiscreteMeasurableSpace J]
    (P : Measure Ω) [IsFiniteMeasure P] (Q : Measure (I → ℝ))
    (G : ℕ → J → MeasurableSpace Ω) (F : ℕ → J → Ω → I → ℝ)
    (K : ℕ → Ω → J) (g : Ω → I → ℝ) (A : Set Ω)
    (hG : ∀ n j, G n j ≤ m) (hMono : ∀ n, Monotone (G n))
    (hF : ∀ n j, Measurable (F n j))
    (hLaw : ∀ n j, Measure.map (F n j) P = Q)
    (hInd : ∀ n j, Indep (G n j) (MeasurableSpace.comap (F n j) inferInstance) P)
    (hLower : ∀ n j, MeasurableSet[G n j] (A ∩ {ω | K n ω ≤ j}))
    (hIndex : ∀ n j, MeasurableSet {ω | K n ω ≤ j})
    (hStable : ∀ ω i, ∀ᶠ n in atTop, F n (K n ω) ω i = g ω i) :
    Measurable g ∧ Measure.map g (P.restrict A) = P A • Q := by sorry
