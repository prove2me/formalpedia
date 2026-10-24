-- Prove2me | Theorems.Thm_K24_Global_pointwiseHaarProjectionSectors
-- name    : K24.Global.pointwiseHaarProjectionSectors
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:59:40.502956+00:00
-- url     : https://prove2.me/theorems/4ba6c8e9-3d8d-4f43-ae4d-704268f0badb
-- title:
--   K24: genuine pointwise Haar projections and zero-average sectors
-- statement:
--   For every smooth four-manifold `M` modeled on the canonical real four-dimensional
--   space `I4`, and every canonical smooth circle action `rho : CircleAction M`, the
--   theorem proves three pointwise Haar projection bundles. The circle measure is
--   the canonical normalized Haar measure. No compactness assumption on `M` is
--   required.
--
--   The tensor assertion quantifies over every actual covariant two-tensor `U`.
--   Its hypothesis is continuity of the function
--   `((p,v),(p,w)) ↦ U(p)(v,w)` on the fiber product of two copies of the actual
--   tangent bundle over the same base point. The public Lean statement expresses
--   this fiber product literally as the subtype of pairs whose base points agree.
--   No symmetry of `U` is required.
--
--   The covector assertion quantifies over every actual covector section `eta`.
--   Its hypothesis is continuity of the evaluation function `(p,v) ↦ eta(p)(v)`
--   on the actual tangent bundle.
--
--   The vector assertion quantifies over every actual vector field `Y`. Its
--   hypothesis is continuity of its actual section map `p ↦ (p,Y(p))` into the
--   tangent bundle. Its pullback is the canonical differential of the inverse
--   action evaluated at the image point.
--
--   For each of these three types, under its stated continuity hypothesis, the
--   corresponding conclusion contains all six assertions:
--
--   1. The original section satisfies the canonical scalar-coordinate Haar
--      integrability predicate in every relevant chart.
--   2. Its canonical average `Pi0` is invariant under every circle pullback.
--   3. That average also satisfies the canonical Haar integrability predicate.
--   4. Averaging the average gives the same average.
--   5. Its canonical complement `PiPerp = section - Pi0 section` satisfies the
--      canonical Haar integrability predicate.
--   6. The complement has zero Haar average.
--
--   The canonical names `IsNonzeroCov2`, `IsNonzeroCovector`, and `IsNonzeroVector`
--   in the final clauses mean zero Haar average, rather than being a nonzero
--   section. All continuity hypotheses are expanded as literal `Continuous`
--   expressions in the public statement; none refers to an unpublished helper
--   predicate or assumes any projection conclusion.
--
--   This theorem serves the pointwise projection and sector clauses of K24. The
--   formal implication from the original canonical chart/Holder regularity
--   predicates to the three continuity hypotheses remains unproved here. Holder
--   regularity and norm estimates for the two projections, the Sobolev estimates,
--   and the remaining full K24 conclusions are also not asserted. The original
--   `FullK24Statement` therefore remains open.
--
--   Supporting the original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §1 common circle projections and §2 fixed slice.

import Definitions.Def_K24GlobalGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open K24.Global
open scoped Manifold ContDiff
universe u

theorem K24.Global.pointwiseHaarProjectionSectors {M : Type u} [TopologicalSpace M]
    [ChartedSpace FourSpace M] [IsManifold I4 ∞ M] (rho : CircleAction M) :
    (∀ U : RawCov2 M,
      Continuous (fun q : {q : TangentBundle I4 M × TangentBundle I4 M //
        q.1.proj = q.2.proj} => U q.val.1.proj q.val.1.2 q.val.2.2) →
      Cov2HaarIntegrable rho U ∧
      IsInvariantCov2 rho (cov2Pi0 rho U) ∧
      Cov2HaarIntegrable rho (cov2Pi0 rho U) ∧
      cov2Pi0 rho (cov2Pi0 rho U) = cov2Pi0 rho U ∧
      Cov2HaarIntegrable rho (cov2PiPerp rho U) ∧
      IsNonzeroCov2 rho (cov2PiPerp rho U)) ∧
    (∀ eta : RawCovector M,
      Continuous (fun q : TangentBundle I4 M => eta q.proj q.2) →
      CovectorHaarIntegrable rho eta ∧
      IsInvariantCovector rho (covectorPi0 rho eta) ∧
      CovectorHaarIntegrable rho (covectorPi0 rho eta) ∧
      covectorPi0 rho (covectorPi0 rho eta) = covectorPi0 rho eta ∧
      CovectorHaarIntegrable rho (covectorPiPerp rho eta) ∧
      IsNonzeroCovector rho (covectorPiPerp rho eta)) ∧
    (∀ Y : RawVector M,
      Continuous (fun p : M => (⟨p, Y p⟩ : TangentBundle I4 M)) →
      VectorHaarIntegrable rho Y ∧
      IsInvariantVector rho (vectorPi0 rho Y) ∧
      VectorHaarIntegrable rho (vectorPi0 rho Y) ∧
      vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y ∧
      VectorHaarIntegrable rho (vectorPiPerp rho Y) ∧
      IsNonzeroVector rho (vectorPiPerp rho Y)) := by sorry
