-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_injective_appTop_of_flat_of_surjective
-- name    : GlobalTheory.ProperFunctions.injective_appTop_of_flat_of_surjective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:32.003908+00:00
-- url     : https://prove2.me/theorems/780cd038-37c0-4a59-a81a-9f374ef06d72
-- title:
--   Proper Functions: injective app Top of flat of surjective
-- statement:
--   The Proper Functions construction uses the injective app Top of flat of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L625-L634
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L625-L634

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

theorem GlobalTheory.ProperFunctions.injective_appTop_of_flat_of_surjective (p : X ⟶ S) [IsAffine S] [Flat p] [Surjective p]
    [QuasiCompact p] : Function.Injective p.appTop := by sorry
