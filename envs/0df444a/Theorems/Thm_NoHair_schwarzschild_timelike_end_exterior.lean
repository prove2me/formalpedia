-- Prove2me | Theorems.Thm_NoHair_schwarzschild_timelike_end_exterior
-- name    : NoHair.schwarzschild_timelike_end_exterior
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T06:58:11.86822+00:00
-- url     : https://prove2.me/theorems/7db9fd01-be6f-4d43-8bbc-c67a783cf29d
-- title:
--   Sharp timelike cutoff and physical Schwarzschild exterior
-- statement:
--   For the ingoing Schwarzschild spacetime of any mass $m>0$, the time-translation vector is timelike throughout the cylinder $A_R=\{r>R\}$ exactly when $R\ge 2m$. For every such $R$, including $R=2m$, the chronological past of $A_R$ and its domain of outer communications both equal the ordinary exterior $\{r>2m\}$. This tests the reference-end correction on the whole Schwarzschild family.
-- source:
--   Schwarzschild time coefficient and horizon: S. Carroll, Lecture Notes on General Relativity, section 7, https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll7.html. P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.2)–(2.4), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.schwarzschild_timelike_end_exterior (m : ℝ) (hm : 0 < m) (R : ℝ) (hR : 0 < R) :
    let S := kerrNewmanSpacetime 0
    let g := kerrNewmanMetricField m 0 0
    let T := kerrNewmanTimeDirection m 0 0
    let A := (Subtype.val : S → E4) ⁻¹' exteriorRegion R
    let D := (Subtype.val : S → E4) ⁻¹' kerrNewmanDOC m 0 0
    ((∀ x ∈ A, g x (coordBasis 0) (coordBasis 0) < 0) ↔ 2*m ≤ R) ∧
      (2*m ≤ R → chronoPastSet g T A = D ∧ domainOfOuterCommunications g T A = D) := by sorry
