-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_exists_ker_fromSpecResidueField
-- name    : GlobalTheory.ProperFunctions.exists_ker_fromSpecResidueField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:16.164959+00:00
-- url     : https://prove2.me/theorems/d3a48419-c6bf-4167-81e8-dc05b3e1033b
-- title:
--   Proper Functions: exists ker from Spec Residue Field
-- statement:
--   The Proper Functions construction uses the exists ker from Spec Residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L289-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L289-L312

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

theorem GlobalTheory.ProperFunctions.exists_ker_fromSpecResidueField [IsAffine S] (𝔭 : Ideal Γ(S, ⊤)) (h𝔭 : 𝔭.IsPrime) :
    ∃ s : S, RingHom.ker (S.fromSpecResidueField s).appTop.hom = 𝔭 := by sorry
