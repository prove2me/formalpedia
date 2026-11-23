-- Prove2me | Theorems.Thm_NoHair_kerr_timelike_radial_reference_exterior
-- name    : NoHair.kerr_timelike_radial_reference_exterior
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T07:24:36.311797+00:00
-- url     : https://prove2.me/theorems/589cffb6-e79f-4e13-a490-264376f24853
-- title:
--   Timelike radial reference regions recover the standard vacuum Kerr exterior
-- statement:
--   In ingoing vacuum Kerr with admissible mass $m$ and spin $a$, let $A_R=\{r>R\}$ and use the canonical future orientation. Suppose the stationary time-translation field is timelike at every point of $A_R$. Its relative domain of outer communications and future event horizon are
--   $$
--   D(A_R)=\{r>r_+\},\qquad H^+(A_R)=\{r=r_+\},\qquad r_+=m+\sqrt{m^2-a^2}.
--   $$
--   The restriction of the metric and field to $D(A_R)$ satisfies the milestone’s Kerr exterior isometry predicate with the original parameters $(m,a,0)$. The statement includes extremal vacuum Kerr.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, p. 7, equations (2.9)–(2.10), https://arxiv.org/abs/0806.0016 . For Kerr see M. Visser, Sections 9–10, https://arxiv.org/abs/0706.0622 . The causal calculation specializes the proved outer-horizon trapping and exterior timelike access lemmas for positive-radius ingoing Kerr.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_timelike_radial_reference_exterior (m a R : ℝ) (hp : IsKerrNewmanBlackHoleParams m a 0)
    (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
    (hφ : ∀ s x, (φ s x).val = x.val + s • coordBasis 0)
    (hsym : IsSymmetryFlow (kerrNewmanMetricField m a 0) (kerrNewmanFieldField a 0) φ)
    (htime : ∀ x : kerrNewmanSpacetime a, R < ksRadius a x.val →
      kerrNewmanMetricField m a 0 x (flowGenerator φ x) (flowGenerator φ x) < 0) :
    let A := {x : kerrNewmanSpacetime a | R < ksRadius a x.val}
    let g := kerrNewmanMetricField m a 0
    let T := kerrNewmanTimeDirection m a 0
    let D := domainOfOuterCommunications g T A
    D = (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a 0 ∧
      futureEventHorizon g T A =
        {x : kerrNewmanSpacetime a | ksRadius a x.val = kerrNewmanOuterRadius m a 0} ∧
      IsKerrNewmanDOC g (kerrNewmanFieldField a 0) D m a 0 := by
  sorry
