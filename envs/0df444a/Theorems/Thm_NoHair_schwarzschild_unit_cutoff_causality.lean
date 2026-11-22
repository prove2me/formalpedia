-- Prove2me | Theorems.Thm_NoHair_schwarzschild_unit_cutoff_causality
-- name    : NoHair.schwarzschild_unit_cutoff_causality
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:44:36.688531+00:00
-- url     : https://prove2.me/theorems/ddc642bf-c57b-4b4d-b191-d17c8ed3de9c
-- title:
--   Causality of the horizon-penetrating Schwarzschild region r > 1
-- statement:
--   In the ingoing mass-one Schwarzschild spacetime $r>0$ let $A=\{r>1\}$ and choose the usual future direction. Then $I^-(A)=A$, $A\subset I^+(A)$, and $A$ is globally hyperbolic. The first equality holds because the region $r\le 1$ is inside the usual horizon at $r=2$, where the areal radius strictly decreases along every future timelike curve. Every point of the open region has nearby timelike predecessors and successors there. In Kruskal coordinates the ingoing patch is the future set $V>0$ and $r>1$ removes a future set of the black-hole interior. Their intersection is causally convex in the globally hyperbolic Kruskal spacetime.
-- source:
--   The definitions AsymptoticallyFlatEnd, domainOfOuterCommunications and IsStaticOn in the NoHair mission. Schwarzschild and Kruskal coordinates and causal geometry in S. Carroll, Lecture Notes on General Relativity, section 7, https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll7.html. The end-relative construction and proper-time obstruction are specific to the formalization.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.schwarzschild_unit_cutoff_causality :
    ∃ T : VecField (kerrNewmanSpacetime 0), IsTimeOrientation (kerrNewmanMetricField 1 0 0) T ∧
      chronoPastSet (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) = ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ∧
      ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ⊆ chronoFutureSet (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ∧
      IsGloballyHyperbolicOn (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) := by sorry
