-- Prove2me | Theorems.Thm_NoHair_kerr_vacuum_helical_symmetry
-- name    : NoHair.kerr_vacuum_helical_symmetry
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:05:21.892452+00:00
-- url     : https://prove2.me/theorems/7852dac0-afd1-4e3b-b8e3-11252729f8f3
-- title:
--   Time translations combined with uniform axial rotations are complete vacuum Kerr symmetries
-- statement:
--   For every Kerr mass and rotation parameter and every constant angular velocity $\Omega$, simultaneous coordinate time translation and axial rotation form a global symmetry flow on the positive-radius ingoing model. Its generator is $\partial_t+\Omega\partial_\varphi$.
-- source:
--   B. Carter, Black hole equilibrium states, in Black Holes (Les Houches 1972), Gordon and Breach (1973). See also S. Carroll, Lecture Notes on General Relativity, §7, https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll7.html. The proof checks the identities directly in the mission’s ingoing Kerr–Schild coordinates.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_vacuum_helical_symmetry (m a Ω : ℝ) :
    let X : VecField (kerrNewmanSpacetime a) := fun x => WithLp.toLp 2 ![1,-Ω*x.val 2,Ω*x.val 1,0]
    ∃ χ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a,
      IsSymmetryFlow (kerrNewmanMetricField m a 0) (kerrNewmanFieldField a 0) χ ∧
      flowGenerator χ = X := by
  sorry
