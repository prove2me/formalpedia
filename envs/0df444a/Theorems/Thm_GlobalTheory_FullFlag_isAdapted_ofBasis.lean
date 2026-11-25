-- Prove2me | Theorems.Thm_GlobalTheory_FullFlag_isAdapted_ofBasis
-- name    : GlobalTheory.FullFlag.isAdapted_ofBasis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:45.868571+00:00
-- url     : https://prove2.me/theorems/a3c22fd1-78db-5e94-96bb-e06694d52d35
-- title:
--   Full Flag: is Adapted of Basis
-- statement:
--   The Full Flag construction uses the is Adapted of Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L252-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L252-L252

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

theorem GlobalTheory.FullFlag.isAdapted_ofBasis (b : Basis (Fin n) R M) : (ofBasis b).IsAdapted b := by sorry
