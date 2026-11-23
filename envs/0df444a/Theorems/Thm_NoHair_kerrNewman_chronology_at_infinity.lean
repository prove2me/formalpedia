-- Prove2me | Theorems.Thm_NoHair_kerrNewman_chronology_at_infinity
-- name    : NoHair.kerrNewman_chronology_at_infinity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T08:33:25.3609+00:00
-- url     : https://prove2.me/theorems/7fe076bb-f9f8-4da2-98ab-cdc694e43677
-- title:
--   Communication with arbitrarily distant regions recovers the Kerr–Newman exterior
-- statement:
--   In the positive-radius ingoing Kerr–Newman spacetime, let $m>0$ and $a^2+e^2\le m^2$ and use the canonical time orientation. For any decreasing family of reference regions mutually cofinal with the regions $r>R$, use any initial cutoff and consider timelike communication to or from arbitrarily far regions. Its chronological past, domain of outer communications and future horizon satisfy
--   $$
--   P_\infty=D_\infty=\{r>r_+\},\qquad H^+_\infty=\{r=r_+\},\qquad
--   r_+=m+\sqrt{m^2-a^2-e^2}.
--   $$
--   The metric and electromagnetic field on $D_\infty$ satisfy the Kerr–Newman exterior isometry predicate with the original parameters. Both Kerr-radius and Cartesian-radius cutoffs qualify. With $\rho$ the Cartesian radius, $\{r>R\}\subseteq\{\rho>R\}$ and $\{\rho>R+|a|\}\subseteq\{r>R\}$.
-- source:
--   For the motivation from reference-region independence see P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, p. 7, immediately after equation (2.10), and Lemma 3.6, https://arxiv.org/abs/0806.0016 . The Kerr–Newman calculation applies the verified outer-horizon trapping theorem, https://prove2.me/theorems/c9973130-c829-4b75-bc23-b60ddc79d7b2 , and timelike access from the exterior, https://prove2.me/theorems/4c5fbcdb-8360-4df5-aa4f-f302e59c0985 .

import Definitions.Def_NoHair_chronologyAtInfinity
import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerrNewman_chronology_at_infinity (m a e R₀ : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    let g := kerrNewmanMetricField m a e
    let T := kerrNewmanTimeDirection m a e
    let A := fun R : ℝ => {x : kerrNewmanSpacetime a | R < ksRadius a x.val}
    let C := fun R : ℝ => (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion R
    let D := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e
    (∀ R, A R ⊆ C R ∧ C (R + |a|) ⊆ A R) ∧
    ∀ B : ℝ → Set (kerrNewmanSpacetime a), Antitone B →
      (∀ R, ∃ S, A S ⊆ B R) → (∀ R, ∃ S, B S ⊆ A R) →
      chronoPastAtInfinity g T B R₀ = D ∧
      domainOfOuterCommunicationsAtInfinity g T B R₀ = D ∧
      futureEventHorizonAtInfinity g T B R₀ =
        {x : kerrNewmanSpacetime a | ksRadius a x.val = kerrNewmanOuterRadius m a e} ∧
      IsKerrNewmanDOC g (kerrNewmanFieldField a e)
        (domainOfOuterCommunicationsAtInfinity g T B R₀) m a e := by
  sorry
