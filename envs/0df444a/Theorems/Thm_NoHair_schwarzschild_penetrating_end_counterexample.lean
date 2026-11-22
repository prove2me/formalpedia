-- Prove2me | Theorems.Thm_NoHair_schwarzschild_penetrating_end_counterexample
-- name    : NoHair.schwarzschild_penetrating_end_counterexample
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:44:48.423341+00:00
-- url     : https://prove2.me/theorems/e587644f-21bf-493a-92aa-2b05169be291
-- title:
--   A horizon-penetrating choice of asymptotic end in the formal Israel 1967 hypotheses
-- statement:
--   Take $m=1$ Schwarzschild in the ingoing Kerr–Schild patch $r>0$ with zero Maxwell field. Choose as the asymptotically flat end the entire coordinate region $A=\{r>1\}$. The definition permits this cutoff to lie inside the ordinary Schwarzschild horizon at $r=2$. Future timelike curves in $r\le1$ cannot return to $A$. Thus the black-hole region defined *relative to this end* is $r\le1$, its boundary $r=1$ is nonempty and connected, and the domain of outer communications is $A$. This region is globally hyperbolic. Stationary time translation is hypersurface-orthogonal everywhere by the stated twist condition.
--
--   There is no isometry from a standard Schwarzschild exterior to $A$. A constant-radius observer exists for unlimited proper time through every point of a standard exterior. At $r=3/2$ in $A$, one of the two directions along any timelike curve of fixed proper-time speed drives $r$ to the lower cutoff in finite time. The counterexample concerns the end-relative formal statement of the 1967 mission. In the usual geometric formulation the domain of outer communications is computed relative to asymptotic infinity.
-- source:
--   The definitions AsymptoticallyFlatEnd, domainOfOuterCommunications and IsStaticOn in the NoHair mission. Schwarzschild and Kruskal coordinates and causal geometry in S. Carroll, Lecture Notes on General Relativity, section 7, https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll7.html. The end-relative construction and proper-time obstruction are specific to the formalization.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.schwarzschild_penetrating_end_counterexample :
    ∃ (T : VecField (kerrNewmanSpacetime 0)) (φ : ℝ → kerrNewmanSpacetime 0 → kerrNewmanSpacetime 0)
      (E : AsymptoticallyFlatEnd (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) φ),
      IsStationaryBlackHole (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) T φ E ∧
      (∀ x, kerrNewmanFieldField 0 0 x = 0) ∧
      IsStaticOn (kerrNewmanMetricField 1 0 0) φ (domainOfOuterCommunications (kerrNewmanMetricField 1 0 0) T E.region) ∧
      ¬ ∃ m : ℝ, 0 < m ∧ IsKerrNewmanDOC (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0)
        (domainOfOuterCommunications (kerrNewmanMetricField 1 0 0) T E.region) m 0 0 := by sorry
