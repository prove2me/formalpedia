-- Prove2me | Theorems.Thm_MFEUnique_Uniq_comparison_step
-- name    : MFEUnique.Uniq.comparison_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:58.650569+00:00
-- url     : https://prove2.me/theorems/2ca35f82-07bf-415e-8eb7-3bbec657ed17
-- title:
--   p. 13, proof of Theorem 1 — θ₁ ⪰SD θ₂ and s₂ ⪰ s₁ imply M_{s₂}θ₂(B) ≤ M_{s₁}θ₁(B) on upper sets, so M_{s₁}θ₁ ⪰SD M_{s₂}θ₂
-- statement:
--   Consider the game under the standing assumptions, with $G$ single-valued and $g$ its selection, and suppose the kernel $Q = Q_g$ is increasing in $x$ and decreasing in $s$ with respect to a binary relation $\succeq$ on $\mathcal P(X)$. Let $\theta_1, \theta_2, s_1, s_2 \in \mathcal P(X)$ with $\theta_1 \succeq_{SD} \theta_2$ and $s_2 \succeq s_1$. Then for every Borel upper set $B$,
--   $$M_{s_2}\theta_2(B) = \int_X Q(x, s_2, B)\,\theta_2(dx) \le \int_X Q(x, s_1, B)\,\theta_2(dx) \le \int_X Q(x, s_1, B)\,\theta_1(dx) = M_{s_1}\theta_1(B),$$
--   and consequently $M_{s_1}\theta_1 \succeq_{SD} M_{s_2}\theta_2$.
--
--   This is the one-step comparison at the heart of the uniqueness proof: monotonicity in $x$ and anti-monotonicity in $s$ combine so that a lower initial distribution under a higher population state stays lower after one transition.
--
--   **Formalization Note** The paper takes $s_1, s_2$ to be MFEs, but the argument does not use it, so that hypothesis is not imposed (a more general statement). The standing assumptions and the single-valuedness of $G$ are kept: they make $x \mapsto g(x, s)$ continuous, so $M_s$ is the true integral and not Lean's junk push-forward. $\succeq_{SD}$ is `StochLE` with swapped arguments.
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, p. 13, proof of Theorem 1, first paragraph and display

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium

open MeasureTheory StochIneqPO.Comparison

namespace MFEUnique.Uniq

/-- p. 13, proof of Theorem 1, first display: if `θ₁ ⪰SD θ₂` and `s₂ ⪰ s₁`, then
`M_{s₂}θ₂(B) ≤ M_{s₁}θ₁(B)` for every upper set `B`, and hence `M_{s₁}θ₁ ⪰SD M_{s₂}θ₂`.
(The proof does not use that `s₁, s₂` are MFEs, so that hypothesis is not imposed.) -/
theorem comparison_step {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]
    (G : Game X q J E A) (hG : G.Standing)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop)
    (g : X → ProbabilityMeasure X → A) (hg : ∀ x s, g x s ∈ G.Gopt x s)
    (hsingle : ∀ x s a, a ∈ G.Gopt x s → a = g x s)
    (hinc : G.IncreasingInX g) (hdec : G.DecreasingInS R g)
    (θ₁ θ₂ s₁ s₂ : ProbabilityMeasure X)
    (hθ : StochLE (θ₂ : Measure X) (θ₁ : Measure X)) (hs : R s₂ s₁) :
    (∀ B : Set X, MeasurableSet B → IsUpperSet B →
        G.Mop g s₂ (θ₂ : Measure X) B ≤ G.Mop g s₁ (θ₁ : Measure X) B) ∧
      StochLE (G.Mop g s₂ (θ₂ : Measure X)) (G.Mop g s₁ (θ₁ : Measure X)) := by sorry

end MFEUnique.Uniq
