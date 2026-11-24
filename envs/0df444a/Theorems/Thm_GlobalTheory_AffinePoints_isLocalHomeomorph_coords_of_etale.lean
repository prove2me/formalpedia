-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_isLocalHomeomorph_coords_of_etale
-- name    : GlobalTheory.AffinePoints.isLocalHomeomorph_coords_of_etale
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:55:00.80138+00:00
-- url     : https://prove2.me/theorems/de28135d-4dbe-4ad5-a996-57db5d7d7308
-- title:
--   Affine Points: is Local Homeomorph coords of etale
-- statement:
--   The Affine Points construction uses the is Local Homeomorph coords of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOpenPartialHomeomorphAnalytic.lean#L233-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOpenPartialHomeomorphAnalytic.lean#L233-L236

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
variable [CompleteSpace 𝕜] {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}

theorem GlobalTheory.AffinePoints.isLocalHomeomorph_coords_of_etale (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale) :
    IsLocalHomeomorph (coords g : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) := by sorry
