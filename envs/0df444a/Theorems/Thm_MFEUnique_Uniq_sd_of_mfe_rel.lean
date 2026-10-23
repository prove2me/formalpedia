-- Prove2me | Theorems.Thm_MFEUnique_Uniq_sd_of_mfe_rel
-- name    : MFEUnique.Uniq.sd_of_mfe_rel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:01.99416+00:00
-- url     : https://prove2.me/theorems/d32c5969-aebe-41f7-92f5-06256e4909da
-- title:
--   p. 13, proof of Theorem 1 — if s₁, s₂ are MFEs with s₂ ⪰ s₁, then s₁ ⪰SD s₂
-- statement:
--   Consider the game under the standing assumptions, with $G$ single-valued and $g$ its selection, and suppose $Q = Q_g$ is $X$-ergodic, increasing in $x$ and decreasing in $s$ with respect to a binary relation $\succeq$ on $\mathcal P(X)$. If $(g_1, s_1)$ and $(g_2, s_2)$ are mean field equilibria with $s_2 \succeq s_1$, then
--   $$s_1 \succeq_{SD} s_2.$$
--
--   This is the comparison half of the uniqueness argument: an MFE that is higher in the relation $\succeq$ cannot be higher in the stochastic order.
--
--   **Formalization Note** The completeness of $\succeq$, its agreement with $\succeq_{SD}$ and its standing property are not used in this step and are not imposed. Each MFE carries its own optimal strategy $g_i$; by single-valuedness of $G$ it coincides with $g$ at $s_i$. $\succeq_{SD}$ is `StochLE` with swapped arguments.
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, p. 13, proof of Theorem 1, third paragraph, first sentence

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium

open MeasureTheory StochIneqPO.Comparison

namespace MFEUnique.Uniq

/-- p. 13, proof of Theorem 1: under Assumption 2(i) and (iii), if `s₁` and `s₂` are two MFEs
with `s₂ ⪰ s₁`, then `s₁ ⪰SD s₂`. -/
theorem sd_of_mfe_rel {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]
    (G : Game X q J E A) (hG : G.Standing)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop)
    (g : X → ProbabilityMeasure X → A) (hg : ∀ x s, g x s ∈ G.Gopt x s)
    (hsingle : ∀ x s a, a ∈ G.Gopt x s → a = g x s)
    (herg : G.IsXErgodic g) (hinc : G.IncreasingInX g) (hdec : G.DecreasingInS R g) :
    ∀ (g₁ g₂ : X → ProbabilityMeasure X → A) (s₁ s₂ : ProbabilityMeasure X),
      G.IsMFE g₁ s₁ → G.IsMFE g₂ s₂ → R s₂ s₁ → StochLE (s₂ : Measure X) (s₁ : Measure X) := by sorry

end MFEUnique.Uniq
