-- Prove2me | Theorems.Thm_MFEUnique_Uniq_comparison_iterate
-- name    : MFEUnique.Uniq.comparison_iterate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:01.655518+00:00
-- url     : https://prove2.me/theorems/7c177e4c-7ad4-42c4-9a77-b77f454583ac
-- title:
--   p. 13, proof of Theorem 1 — θ₁ ⪰SD θ₂ and s₂ ⪰ s₁ imply M^n_{s₁}θ₁ ⪰SD M^n_{s₂}θ₂ for all n
-- statement:
--   Under the hypotheses of the one-step comparison (standing assumptions, $G$ single-valued with selection $g$, $Q$ increasing in $x$ and decreasing in $s$), let $\theta_1 \succeq_{SD} \theta_2$ and $s_2 \succeq s_1$. Then for every $n$,
--   $$M_{s_1}^n\theta_1 \succeq_{SD} M_{s_2}^n\theta_2.$$
--
--   Iterating the comparison is what lets the stochastic order pass to the long-run distributions $\mu_{s_1}$ and $\mu_{s_2}$.
--
--   **Formalization Note** The statement holds for every $n \in \mathbb N$ including $n = 0$, where it is the hypothesis $\theta_1 \succeq_{SD} \theta_2$; the paper's $n \in \mathbb N$ starts at $1$. $\succeq_{SD}$ is `StochLE` with swapped arguments.
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, p. 13, proof of Theorem 1, second paragraph, first sentence

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium

open MeasureTheory StochIneqPO.Comparison

namespace MFEUnique.Uniq

/-- p. 13, proof of Theorem 1: if `θ₁ ⪰SD θ₂` and `s₂ ⪰ s₁`, then
`M^n_{s₁}θ₁ ⪰SD M^n_{s₂}θ₂` for every `n`. (The case `n = 0` is the hypothesis itself.) -/
theorem comparison_iterate {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]
    (G : Game X q J E A) (hG : G.Standing)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop)
    (g : X → ProbabilityMeasure X → A) (hg : ∀ x s, g x s ∈ G.Gopt x s)
    (hsingle : ∀ x s a, a ∈ G.Gopt x s → a = g x s)
    (hinc : G.IncreasingInX g) (hdec : G.DecreasingInS R g)
    (θ₁ θ₂ s₁ s₂ : ProbabilityMeasure X)
    (hθ : StochLE (θ₂ : Measure X) (θ₁ : Measure X)) (hs : R s₂ s₁) :
    ∀ n : ℕ, StochLE ((G.Mop g s₂)^[n] (θ₂ : Measure X)) ((G.Mop g s₁)^[n] (θ₁ : Measure X)) := by sorry

end MFEUnique.Uniq
