-- Prove2me | Theorems.Thm_LipschitzOnWith_exists_cover_image_unitCube
-- name    : LipschitzOnWith.exists_cover_image_unitCube
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:32:25.096283+00:00
-- url     : https://prove2.me/theorems/095c0e70-6e2b-4d85-94ca-08a25d4acc82
-- title:
--   A quantitative cover of a Lipschitz cube image
-- statement:
--   Let $E$ be a pseudo metric space, let $C\ge0$, and let $f:\mathbb R^d\to E$ be $C$-Lipschitz on $[0,1]^d$, where the domain uses the supremum norm. For every integer $m\ge1$ there are sets $T_k\subseteq E$, indexed by $k\in\{0,\ldots,m-1\}^d$, such that
--
--   $$
--   f([0,1]^d)\subseteq\bigcup_k T_k,\qquad
--   \operatorname{dist}(x,y)\le\frac Cm\quad(x,y\in T_k).
--   $$
--
--   Thus the image has a cover by $m^d$ sets with the stated diameter bound.
--
--   This gives explicit covering numbers and diameters for each Lipschitz chart.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Topology/MetricSpace/LipschitzParametrizable.lean#L340-L395) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Topology/MetricSpace/LipschitzParametrizable.lean#L340-L395

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Topology_MetricSpace_LipschitzParametrizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Lipschitz-parametrizable sets

A set is Lipschitz parametrizable in dimension `d` when finitely many Lipschitz images of the
unit `d`-cube cover it.  This is the boundary regularity condition used in lattice-point counting:
a codimension-one parametrization gives quantitative control on how many lattice cells can meet a
boundary.

This file supplies the elementary API needed to assemble parametrizations: the property is
monotone in the set, is preserved by Lipschitz images, by locally Lipschitz images, by products
and by finite unions, and holds for finite sets.
It also supplies the way in from smoothness: a map that is `C¹` on the compact cube is Lipschitz
there, so the image of a cube of the right dimension is a single chart.
It also records the basic dimension consequence.  A Lipschitz-parametrizable subset of a
finite-dimensional real normed space has additive Haar measure zero whenever the parameter
dimension is strictly smaller than the ambient dimension.  The proof compares additive Haar
measure with Hausdorff measure and uses the fact that Lipschitz maps do not increase Hausdorff
dimension.

It also records the quantitative form of a single chart: cutting the unit `d`-cube into `m ^ d`
subcubes of side `1 / m` covers a Lipschitz image of it by `m ^ d` pieces of diameter `C / m`.
That is what turns a parametrization in a given dimension into a count.

## Main declarations

* `TauCeti.IsLipschitzParametrizable`: finite Lipschitz parametrizability by a
  unit cube;
* `TauCeti.isLipschitzParametrizable_iff`: the finite-chart characterization of the predicate;
* `TauCeti.IsLipschitzParametrizable.union`: closure under binary unions;
* `TauCeti.IsLipschitzParametrizable.image`: closure under Lipschitz images;
* `TauCeti.IsLipschitzParametrizable.image_of_locallyLipschitz`: closure under locally Lipschitz
  images, which is what a chart-by-chart compactness argument buys over `image`;
* `TauCeti.IsLipschitzParametrizable.iUnion`: closure under unions over a finite index type;
* `TauCeti.IsLipschitzParametrizable.prod`: a product is parametrized in the sum of the
  dimensions;
* `TauCeti.IsLipschitzParametrizable.image_unitCube_of_contDiffOn`: a unit cube's image under a
  map that is `C¹` on it is parametrized by that cube;
* `TauCeti.IsLipschitzParametrizable.of_isBounded`: a bounded subset of a finite-dimensional real
  normed space is parametrized in the ambient dimension;
* `TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker`: a bounded subset of a hyperplane
  is parametrized in codimension one;
* `TauCeti.IsLipschitzParametrizable.measure_zero`: a parametrized set has
  additive Haar measure zero below the ambient dimension;
* `LipschitzOnWith.exists_cover_image_unitCube`: a Lipschitz image of the unit `d`-cube is
  covered by `m ^ d` pieces of arbitrarily small diameter.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2, which the definition and its use in
  the lattice-point estimate follow.
* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, whose
  `exists_lipschitz_cube_cover_hyperplane_slab` is the concrete precursor of
  `of_isBounded` and `of_isBounded_of_subset_ker`: it covers a bounded slab of a coordinate
  hyperplane of `ι → ℝ` by a single chart, through the same affine rescaling
  `c ↦ 2 * M * c - M` of the unit cube onto the box `[-M, M]`. The two lemmas here say the
  same thing without reference to coordinates, for any finite-dimensional real normed space
  and any hyperplane in it.
-/

 section

open MeasureTheory Set

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti





namespace TauCeti.IsLipschitzParametrizable
end TauCeti.IsLipschitzParametrizable
section IsLipschitzParametrizable
open TauCeti TauCeti.IsLipschitzParametrizable

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
  {d : ℕ} {S T : Set E}





























end IsLipschitzParametrizable

end TauCeti

namespace LipschitzOnWith
end LipschitzOnWith
section LipschitzOnWith
open LipschitzOnWith

variable {E : Type*} [PseudoMetricSpace E]

theorem LipschitzOnWith.exists_cover_image_unitCube {d : ℕ} {C : _root_.NNReal} {f : (_root_.Fin d → ℝ) → E}
    (hf : _root_.LipschitzOnWith C f (_root_.Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) :
    ∃ T : (_root_.Fin d → _root_.Fin m) → _root_.Set E,
      (f '' _root_.Set.Icc (0 : _root_.Fin d → ℝ) 1 ⊆ ⋃ k, T k) ∧
        ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, _root_.Dist.dist x y ≤ C / m := by sorry
