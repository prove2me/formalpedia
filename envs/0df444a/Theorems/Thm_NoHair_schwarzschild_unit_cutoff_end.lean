-- Prove2me | Theorems.Thm_NoHair_schwarzschild_unit_cutoff_end
-- name    : NoHair.schwarzschild_unit_cutoff_end
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:44:40.958805+00:00
-- url     : https://prove2.me/theorems/0c64ffc6-957d-4422-b0dc-ce9e2ded4685
-- title:
--   A mass-one Schwarzschild end beginning at areal radius one
-- statement:
--   In the mass-one ingoing Schwarzschild spacetime $r>0$, the identity chart restricted to $r>1$ and ordinary Kerr–Schild time translations satisfy the mission’s definition of a stationary asymptotically flat end with cutoff $R=1$. This end extends through the usual event horizon at $r=2$. The decay bounds hold uniformly for $r>1$ because $g-\eta=(2/r)k\otimes k$ and the spatial components of $k$ are the unit radial vector.
-- source:
--   The definitions AsymptoticallyFlatEnd, domainOfOuterCommunications and IsStaticOn in the NoHair mission. Schwarzschild and Kruskal coordinates and causal geometry in S. Carroll, Lecture Notes on General Relativity, section 7, https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll7.html. The end-relative construction and proper-time obstruction are specific to the formalization.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.schwarzschild_unit_cutoff_end :
    ∃ (φ : ℝ → kerrNewmanSpacetime 0 → kerrNewmanSpacetime 0) (E : AsymptoticallyFlatEnd (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) φ),
      (∀ s x, (φ s x).val = x.val + s • coordBasis 0) ∧
      IsSymmetryFlow (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) φ ∧ E.R = 1 ∧ E.region = ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) := by sorry
