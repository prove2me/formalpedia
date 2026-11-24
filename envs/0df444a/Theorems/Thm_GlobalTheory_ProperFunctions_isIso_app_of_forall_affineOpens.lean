-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_app_of_forall_affineOpens
-- name    : GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:23.539257+00:00
-- url     : https://prove2.me/theorems/acf1cca5-b931-4e97-ab89-1044d7e39932
-- title:
--   Proper Functions: is Iso app of forall affine Opens
-- statement:
--   The Proper Functions construction uses the is Iso app of forall affine Opens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L436-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L436-L438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}}

theorem GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens (p : X ⟶ S)
    (h : ∀ U : S.affineOpens, IsIso (p ∣_ U.1).appTop) (U : S.Opens) : IsIso (p.app U) := by sorry
