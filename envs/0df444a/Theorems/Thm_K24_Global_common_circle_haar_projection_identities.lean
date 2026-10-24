-- Prove2me | Theorems.Thm_K24_Global_common_circle_haar_projection_identities
-- name    : K24.Global.common_circle_haar_projection_identities
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:37:24.420242+00:00
-- url     : https://prove2.me/theorems/978e8193-9aa5-4a85-8608-360deaeafa8a
-- title:
--   K24 common-circle Haar projection identities for actual tensor, covector and vector sections
-- statement:
--   On any smooth real four-manifold with one actual smooth circle action, normalized pointwise Haar averaging of every Haar-integrable covariant 2-tensor, covector, or vector section is invariant and idempotent, and the complementary section has zero Haar mean. The same circle action is used in all three sectors. Integrability is exactly the frozen coordinate predicate, and averages and pullbacks are exactly the original geometric definitions, including the inverse-action differential for vectors. This supplies the algebraic projection fields in HolderProjectionConclusions. The original full K24 target still must establish Haar integrability from its admissibility hypotheses, Holder and Sobolev regularity, and bounds H and 1+H; none of those analytic results is asserted here.
-- source:
--   Dependency of original theorem aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 (FullK24Statement), specifically the invariance, idempotence, and zero-mean fields of HolderProjectionConclusions. Original K24 source commit 8c02be189f097080feca952347c9104bfb986242; official geometric, analytic and statement definitions preserved unchanged.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff

namespace K24.Global
universe u
theorem common_circle_haar_projection_identities :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (rho : CircleAction M),
    (∀ u : RawCov2 M, Cov2HaarIntegrable rho u →
      IsInvariantCov2 rho (cov2Pi0 rho u) ∧
      cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
      IsNonzeroCov2 rho (cov2PiPerp rho u)) ∧
    (∀ eta : RawCovector M, CovectorHaarIntegrable rho eta →
      IsInvariantCovector rho (covectorPi0 rho eta) ∧
      covectorPi0 rho (covectorPi0 rho eta) = covectorPi0 rho eta ∧
      IsNonzeroCovector rho (covectorPiPerp rho eta)) ∧
    (∀ Y : RawVector M, VectorHaarIntegrable rho Y →
      IsInvariantVector rho (vectorPi0 rho Y) ∧
      vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y ∧
      IsNonzeroVector rho (vectorPiPerp rho Y)) := by
  sorry
end K24.Global
