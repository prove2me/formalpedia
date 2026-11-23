-- Prove2me | Theorems.Thm_NoHair_subextremal_kerr_realizes_timelike_end_uniqueness
-- name    : NoHair.subextremal_kerr_realizes_timelike_end_uniqueness
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:05:32.88283+00:00
-- url     : https://prove2.me/theorems/b58c58b1-5a12-4446-90e3-20e8abc4ac38
-- title:
--   Every subextremal vacuum Kerr black hole realizes all hypotheses of the timelike-end uniqueness problem
-- statement:
--   For every $m>0$ and $|a|<m$, the ingoing vacuum Kerr model admits a stationary reference end on which the stationary field is everywhere timelike. It satisfies all the standing hypotheses of the proposed analytic vacuum uniqueness statement. Its domain is the Kerr exterior $r>r_+$, its connected future horizon is $r=r_+$, and the outer generator has strictly positive surface gravity $(r_+-m)/(r_+^2+a^2)$. This verifies the hypotheses and the isometry conclusion throughout the subextremal Kerr family, including Schwarzschild.
-- source:
--   B. Carter, Black hole equilibrium states, in Black Holes (Les Houches 1972), Gordon and Breach (1973). See also S. Carroll, Lecture Notes on General Relativity, §7, https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll7.html. The proof checks the identities directly in the mission’s ingoing Kerr–Schild coordinates.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.subextremal_kerr_realizes_timelike_end_uniqueness (m a : ℝ) (hm : 0 < m) (hsub : a^2 < m^2) :
    let g := kerrNewmanMetricField m a 0
    let F := kerrNewmanFieldField a 0
    let T := kerrNewmanTimeDirection m a 0
    let R := kerrNewmanOuterRadius m a 0
    ∃ (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a) (E : AsymptoticallyFlatEnd g F φ),
      (∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0) ∧
      IsStationaryBlackHole g F T φ E ∧ (∀ x, F x = 0) ∧ IsAnalyticBilinField g ∧
      (domainOfOuterCommunications g T E.region = (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a 0) ∧
      (futureEventHorizon g T E.region = {x : kerrNewmanSpacetime a | ksRadius a x.val = R}) ∧
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region) (domainOfOuterCommunications g T E.region) ∧
      0 < (R-m)/(R^2+a^2) ∧ IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0 := by
  sorry
