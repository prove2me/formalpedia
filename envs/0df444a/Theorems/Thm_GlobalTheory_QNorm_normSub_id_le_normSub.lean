-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_normSub_id_le_normSub
-- name    : GlobalTheory.QNorm.normSub_id_le_normSub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:24.519032+00:00
-- url     : https://prove2.me/theorems/281c3720-9d45-43ea-b30a-726183d771c4
-- title:
--   QNorm: norm Sub id le norm Sub
-- statement:
--   The QNorm construction uses the norm Sub id le norm Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitsSupUnitsLocalNormsSqrtNeTop.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitsSupUnitsLocalNormsSqrtNeTop.lean#L11-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.normSub_id_le_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) :
    normSub (RingHom.id F) δ ≤ normSub φ δ := by sorry
