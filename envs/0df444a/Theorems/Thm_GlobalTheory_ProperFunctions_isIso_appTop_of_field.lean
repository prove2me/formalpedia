-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_field
-- name    : GlobalTheory.ProperFunctions.isIso_appTop_of_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:35.074467+00:00
-- url     : https://prove2.me/theorems/74f10bfe-2a69-44e8-952f-7237bb5c4170
-- title:
--   Proper Functions: is Iso app Top of field
-- statement:
--   The Proper Functions construction uses the is Iso app Top of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L172-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L172-L180

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
variable {X S : Scheme.{u}}

theorem GlobalTheory.ProperFunctions.isIso_appTop_of_field {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [GeometricallyIntegral p] [UniversallyClosed p] : IsIso p.appTop := by sorry
