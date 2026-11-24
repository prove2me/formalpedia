-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_det_eq_det_submatrix_of_row_eq_single
-- name    : FunctorialResolution.EmbeddedResolution.det_eq_det_submatrix_of_row_eq_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:58:38.814915+00:00
-- url     : https://prove2.me/theorems/6f7683aa-5b86-46fd-9d8a-07cfb9bf7d62
-- title:
--   Embedded Resolution: det eq det submatrix of row eq single
-- statement:
--   The Embedded Resolution construction uses the det eq det submatrix of row eq single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/DerivationLiftAndDeterminant.lean#L131-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/DerivationLiftAndDeterminant.lean#L131-L147

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_DerivationLiftAndDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem FunctorialResolution.EmbeddedResolution.det_eq_det_submatrix_of_row_eq_single (e : ι ≃ Fin (n + 1)) (M : Matrix ι ι R)
    (h : ∀ b : ι, M (e.symm 0) b = if b = e.symm 0 then (1 : R) else 0) :
    M.det =
      (M.submatrix (fun i : Fin n => e.symm i.succ) (fun i : Fin n => e.symm i.succ)).det := by sorry
