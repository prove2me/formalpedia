-- Prove2me | Theorems.Thm_NoHair_kerr_inner_end_communication_at_infinity
-- name    : NoHair.kerr_inner_end_communication_at_infinity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T08:39:14.143427+00:00
-- url     : https://prove2.me/theorems/fbdb2742-9ce4-43f2-9288-8ff3b30b2466
-- title:
--   Finite-region and arbitrarily far communication on the same vacuum Kerr counterexample
-- statement:
--   On positive-radius ingoing vacuum Kerr with $m=5/2$ and $a=2$, there is a single stationary asymptotically flat end $E$ with cutoff $1$ whose chart sends every coordinate tail $\rho>R$ to $r>R$ for $R\ge1$. The original milestone hypotheses hold for this $E$, including analyticity, vanishing electromagnetic field, and nondegeneracy of its relative future horizon. The domain computed relative to $E$ alone is $r>1$, its horizon is $r=1$, and that domain admits no standard vacuum Kerr exterior isometry for any admissible mass and spin.
--
--   On precisely the same input, requiring timelike communication with arbitrarily distant tails gives $D_\infty=\{r>4\}$ and $H^+_\infty=\{r=4\}$. The metric and field on $D_\infty$ satisfy the standard Kerr exterior predicate with the original parameters.
-- source:
--   For the motivation from reference-region independence see P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, p. 7, immediately after equation (2.10), and Lemma 3.6, https://arxiv.org/abs/0806.0016 . For the explicit counterexample and its timelike-curve obstruction see https://prove2.me/theorems/c4698ceb-01fb-4c66-997c-a1115474b338 .

import Definitions.Def_NoHair_chronologyAtInfinity
import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_inner_end_communication_at_infinity :
    let g := kerrNewmanMetricField (5/2) 2 0
    let F := kerrNewmanFieldField 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    ∃ (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
      (E : AsymptoticallyFlatEnd g F φ),
      let B := fun R : ℝ => E.ψ '' exteriorRegion R
      let D := domainOfOuterCommunications g T E.region
      let H := futureEventHorizon g T E.region
      let Dinf := domainOfOuterCommunicationsAtInfinity g T B E.R
      let Hinf := futureEventHorizonAtInfinity g T B E.R
      E.R = 1 ∧
      (∀ R, E.R ≤ R → B R = {x : kerrNewmanSpacetime 2 | R < ksRadius 2 x.val}) ∧
      IsStationaryBlackHole g F T φ E ∧ (∀ x, F x = 0) ∧ IsAnalyticBilinField g ∧
      IsNondegenerateHorizon g F H D ∧
      D = {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val} ∧
      H = {x : kerrNewmanSpacetime 2 | ksRadius 2 x.val = 1} ∧
      (∀ μ a : ℝ, IsKerrNewmanBlackHoleParams μ a 0 → ¬ IsKerrNewmanDOC g F D μ a 0) ∧
      Dinf = {x : kerrNewmanSpacetime 2 | 4 < ksRadius 2 x.val} ∧
      Hinf = {x : kerrNewmanSpacetime 2 | ksRadius 2 x.val = 4} ∧
      IsKerrNewmanDOC g F Dinf (5/2) 2 0 := by
  sorry
