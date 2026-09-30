-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_fundamentalCone_isLipschitzParametrizable_frontier_normLeOne
-- name    : NumberField.mixedEmbedding.fundamentalCone.isLipschitzParametrizable_frontier_normLeOne
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:47:11.92723+00:00
-- url     : https://prove2.me/theorems/7f7c0a8f-2961-46b9-a177-b08747103927
-- title:
--   A Lipschitz boundary for the unit fundamental-cone norm section
-- statement:
--   Let $K$ be a number field of degree $n$, with Minkowski space $V_K=\mathbb R^{r_1}\times\mathbb C^{r_2}$. Let $D_K$ be the norm-at-most-one section of the standard unit fundamental cone, defined using a fundamental domain for the logarithmic unit lattice. Then
--
--   $$
--   \partial D_K\ \text{is covered by finitely many Lipschitz images of }[0,1]^{n-1}.
--   $$
--
--   The norm here is the multiplicative archimedean norm, with complex-place factors squared.
--
--   This supplies a quantitative boundary regularity condition for counting integral points in the fundamental cone.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/NormLeOneLipschitz.lean#L303-L326) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/NormLeOneLipschitz.lean#L303-L326

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_CanonicalEmbedding_NormLeOneLipschitz
import Definitions.Def_TauCeti_Topology_MetricSpace_LipschitzParametrizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A Lipschitz parametrization of the frontier of the norm-≤-one region

`TauCeti.NumberTheory.GeometryOfNumbers.LatticePointCount` counts lattice points in a dilated
region with a power-saving error, but only for regions whose frontier is Lipschitz
parametrizable: `exists_abs_ncard_smul_inter_vadd_sub_le` takes
`IsLipschitzParametrizable (finrank ℝ E - 1) (frontier D)` as a hypothesis. Mathlib proves that
`frontier (normLeOne K)` is *null* (`volume_frontier_normLeOne`), which is what a rate-free limit
needs and is strictly weaker: a null frontier does not provide a quantitative or power-saving
error bound.

This file discharges that hypothesis for `normLeOne K`. Mathlib presents the region through
`expMapBasis`, a partial homeomorphism of `realSpace K` whose image of the box
`paramSet K = univ.pi fun w ↦ if w = w₀ then Iic 0 else Ico 0 1` is the norm-≤-one region up to
`normAtAllPlaces`. The frontier of a box is the union of its faces, so a Lipschitz cover of the
image reduces to parametrizing the image of each face — which is what the maps here do.

The `w₀` face is where the unbounded `Iic 0` direction is pinned at its endpoint; the side faces
pin one of the bounded `Ico 0 1` directions, and there the substitution `t = exp (x w₀)` turns the
unbounded direction into the freed cube coordinate.

## Main results

* `isLipschitzParametrizable_frontier_normLeOne`: the frontier of `normLeOne K` is Lipschitz
  parametrizable in dimension `finrank ℝ (mixedSpace K) - 1`, one less than that of the mixed
  space.
* `frontier_normLeOne_subset_preimage`: that frontier lies over the frontier of the box image,
  through `normAtAllPlaces`.
* `isLipschitzParametrizable_frontier_image_paramSet`: the frontier of the box image is Lipschitz
  parametrizable in dimension `rank K`, one less than that of `realSpace K`.
* `contDiff_expMapBasis`: the box parametrization is smooth.
* `closure_image_paramSet_subset`: the closure of the box image adds only the origin.
* `frontier_image_paramSet_subset`: the frontier of the box image lies in the image of the box's
  frontier, together with the origin.

The face maps that decompose the box's frontier, the lifts that cover the fibres of
`normAtAllPlaces`, and the lemmas supporting them, are `private`: they implement the
parametrization and are not independently reusable.

## References

* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean`, from which the face
  decomposition is adapted: `faceMapZero`, `faceMapSide`, `contDiff_faceMapZero`,
  `contDiff_faceMapSide`, `frontier_image_subset_of_closure_subset` and
  `frontier_image_paramSet_subset` follow that file's declarations of the same names.
  `isLipschitzParametrizable_frontier_normLeOne` is that file's
  `normLeOne_frontier_lipschitz_cover`, and the circle direction of `liftMap` follows its
  `lipschitzWith_exp_ofReal_mul_I`; the sign and angle bookkeeping is arranged differently here,
  through a single globally `C¹` lift rather than that file's `cubeRelabel` scaffolding.
-/

 section

open Finset Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem
open scoped NumberField

namespace NumberField.mixedEmbedding.fundamentalCone
end NumberField.mixedEmbedding.fundamentalCone
section NumberField.mixedEmbedding.fundamentalCone
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]















variable {K}





variable (K)















open scoped Classical

theorem NumberField.mixedEmbedding.fundamentalCone.isLipschitzParametrizable_frontier_normLeOne :
    _root_.TauCeti.IsLipschitzParametrizable (_root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K) - 1) (_root_.frontier (_root_.NumberField.mixedEmbedding.fundamentalCone.normLeOne K)) := by sorry
