-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_infinite_norm_one
-- name    : GlobalTheory.UnRep.infinite_norm_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:25:34.197162+00:00
-- url     : https://prove2.me/theorems/0c4f3566-f12b-4e41-af81-4839425ee583
-- title:
--   Un Rep: infinite norm one
-- statement:
--   The Un Rep construction uses the infinite norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L112-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep

theorem GlobalTheory.UnRep.infinite_norm_one {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E] (c : E ≃ₐ[F] E)
    (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) : {l : E | l * c l = 1}.Infinite := by sorry
