-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_hasDerivAt_aevalTower_line
-- name    : GlobalTheory.AffinePoints.hasDerivAt_aevalTower_line
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:57.494942+00:00
-- url     : https://prove2.me/theorems/43049853-cd94-4cb8-b060-b6dbf0fc04e4
-- title:
--   Affine Points: has Deriv At aeval Tower line
-- statement:
--   The Affine Points construction uses the has Deriv At aeval Tower line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOpenPartialHomeomorphAnalytic.lean#L26-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOpenPartialHomeomorphAnalytic.lean#L26-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

theorem GlobalTheory.AffinePoints.hasDerivAt_aevalTower_line {R ι : Type*} [CommRing R] [Algebra 𝕜 R] [Fintype ι]
    (φ : R →ₐ[𝕜] 𝕜) (q : MvPolynomial ι R) (y v : ι → 𝕜) :
    HasDerivAt (fun t : 𝕜 => (aevalTower φ (y + t • v) : MvPolynomial ι R →ₐ[𝕜] 𝕜) q)
      (∑ i, (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv i q) * v i) 0 := by sorry
