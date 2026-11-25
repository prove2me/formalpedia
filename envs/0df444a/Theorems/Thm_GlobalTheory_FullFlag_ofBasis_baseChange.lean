-- Prove2me | Theorems.Thm_GlobalTheory_FullFlag_ofBasis_baseChange
-- name    : GlobalTheory.FullFlag.ofBasis_baseChange
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:04.429606+00:00
-- url     : https://prove2.me/theorems/93bd79d2-47e9-4398-b065-82a745dd55d6
-- title:
--   Full Flag: of Basis base Change
-- statement:
--   The Full Flag construction uses the of Basis base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L358-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L358-L363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}

theorem GlobalTheory.FullFlag.ofBasis_baseChange (b : Basis (Fin n) R M) (S : Type*) [CommRing S] [Algebra R S] :
    ofBasis (b.baseChange S) = (ofBasis b).baseChange S := by sorry
