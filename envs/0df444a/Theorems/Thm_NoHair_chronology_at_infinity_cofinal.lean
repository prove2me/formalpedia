-- Prove2me | Theorems.Thm_NoHair_chronology_at_infinity_cofinal
-- name    : NoHair.chronology_at_infinity_cofinal
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T08:33:26.519803+00:00
-- url     : https://prove2.me/theorems/af90b817-6909-4205-9371-1bb2fc368101
-- title:
--   Timelike communication with an end is invariant under cofinal choices of reference regions
-- statement:
--   Let $A_R$ and $B_S$ be decreasing families of reference regions in a spacetime. Suppose that each $A_R$ contains some $B_S$ and each $B_S$ contains some $A_R$. For any two initial cutoffs, the points that can send timelike signals to arbitrarily far regions agree for the two families, as do the points that can receive such signals. Consequently the two domains of outer communications and the two future horizons defined at infinity agree. The domain at infinity is contained in the ordinary domain computed relative to the single region at the initial cutoff. Taking $A=B$ shows independence of that cutoff in any spacetime.
-- source:
--   For the motivation from reference-region independence see P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, p. 7, immediately after equation (2.10), and Lemma 3.6, https://arxiv.org/abs/0806.0016 . The cofinal-family statement here is a direct consequence of monotonicity of the chronological future and past of a set.

import Definitions.Def_NoHair_chronologyAtInfinity

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.chronology_at_infinity_cofinal {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (T : VecField M)
    (A B : ℝ → Set M) (a b : ℝ) (hA : Antitone A) (hB : Antitone B)
    (hAB : ∀ R, ∃ S, B S ⊆ A R) (hBA : ∀ S, ∃ R, A R ⊆ B S) :
    chronoPastAtInfinity g T A a = chronoPastAtInfinity g T B b ∧
    chronoFutureAtInfinity g T A a = chronoFutureAtInfinity g T B b ∧
    domainOfOuterCommunicationsAtInfinity g T A a = domainOfOuterCommunicationsAtInfinity g T B b ∧
    futureEventHorizonAtInfinity g T A a = futureEventHorizonAtInfinity g T B b ∧
    domainOfOuterCommunicationsAtInfinity g T A a ⊆ domainOfOuterCommunications g T (A a) := by
  sorry
