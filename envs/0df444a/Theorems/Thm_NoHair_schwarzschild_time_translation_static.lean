-- Prove2me | Theorems.Thm_NoHair_schwarzschild_time_translation_static
-- name    : NoHair.schwarzschild_time_translation_static
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:44:40.50525+00:00
-- url     : https://prove2.me/theorems/acc1324e-134a-4fe8-ac1c-06151b2e87aa
-- title:
--   Schwarzschild time translation is hypersurface-orthogonal across the horizon
-- statement:
--   In ingoing Schwarzschild coordinates at mass one, every flow acting by Kerr–Schild time translation has hypersurface-orthogonal generator throughout $r>0$, including the horizon and the trapped interior. Its lowered one-form is $(-1+2/r)\,dt+(2/r)\,dr$. The exterior derivative is a multiple of $dr\wedge dt$, so the Frobenius three-form vanishes. This is precisely the predicate IsStaticOn used by the mission.
-- source:
--   The definitions AsymptoticallyFlatEnd, domainOfOuterCommunications and IsStaticOn in the NoHair mission. Schwarzschild and Kruskal coordinates and causal geometry in S. Carroll, Lecture Notes on General Relativity, section 7, https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll7.html. The end-relative construction and proper-time obstruction are specific to the formalization.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.schwarzschild_time_translation_static (φ : ℝ → kerrNewmanSpacetime 0 → kerrNewmanSpacetime 0)
    (hφ : ∀ s x, (φ s x).val = x.val + s • coordBasis 0) :
    IsStaticOn (kerrNewmanMetricField 1 0 0) φ Set.univ := by sorry
