-- Prove2me | Theorems.Thm_NoHair_schwarzschild_trapped_shell_not_exterior
-- name    : NoHair.schwarzschild_trapped_shell_not_exterior
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:44:41.405807+00:00
-- url     : https://prove2.me/theorems/bdb530c8-38ea-4529-9bda-e87f9f495f18
-- title:
--   A Schwarzschild domain containing a trapped shell is not a Schwarzschild exterior
-- statement:
--   For the ingoing mass-one Schwarzschild metric on $A=\{r>1\}$, no diffeomorphism from a complete standard Schwarzschild exterior of any mass $m>0$ pulls back the metric as required by the mission’s definition. Each standard exterior point lies on an all-time timelike stationary orbit with constant proper-time speed. For $1<r\le3/2$ in the mass-one spacetime, a timelike tangent $v$ obeys $dr(v)^2\ge(2/r-1)(-g(v,v))$. Hence no two-sided timelike curve with constant negative squared speed can stay in $A$ and pass through $r=3/2$. This distinguishes the geometries without assuming that a proposed isometry preserves time translations or the radius.
-- source:
--   The definitions AsymptoticallyFlatEnd, domainOfOuterCommunications and IsStaticOn in the NoHair mission. Schwarzschild and Kruskal coordinates and causal geometry in S. Carroll, Lecture Notes on General Relativity, section 7, https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll7.html. The end-relative construction and proper-time obstruction are specific to the formalization.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.schwarzschild_trapped_shell_not_exterior (m : ℝ) (hm : 0 < m) :
    ¬ IsKerrNewmanDOC (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) m 0 0 := by sorry
