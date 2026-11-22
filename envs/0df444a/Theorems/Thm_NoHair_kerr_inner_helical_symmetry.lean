-- Prove2me | Theorems.Thm_NoHair_kerr_inner_helical_symmetry
-- name    : NoHair.kerr_inner_helical_symmetry
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T23:06:58.667519+00:00
-- url     : https://prove2.me/theorems/096cbc57-7721-4c99-9600-e638c77d8082
-- title:
--   The complete helical Killing flow of the inner Kerr horizon
-- statement:
--   In Kerr–Schild Cartesian coordinates on the positive-radius $m=5/2$, $a=2$ vacuum Kerr space, simultaneous time translation and planar rotation by angle $2s/5$ defines a complete symmetry group. Its generator is $X=(1,-2y/5,2x/5,0)$, the helical Killing field of the inner horizon.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, §§4 and 9, in particular equations (107)–(115), https://arxiv.org/abs/0706.0622. B. Carter, Global Structure of the Kerr Family of Gravitational Fields, Phys. Rev. 174 (1968) 1559–1571, https://doi.org/10.1103/PhysRev.174.1559.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_inner_helical_symmetry :
    let X : VecField (kerrNewmanSpacetime 2) := fun x => WithLp.toLp 2 ![1, -(2/5)*x.val 2, (2/5)*x.val 1, 0]
    ∃ χ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2,
      IsSymmetryFlow (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0) χ ∧
      flowGenerator χ=X := by
  sorry
