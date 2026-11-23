-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_val_integer_le_one
-- name    : GlobalTheory.QNorm.val_integer_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:19.479798+00:00
-- url     : https://prove2.me/theorems/04ae621a-cc2d-4637-9424-320a93927160
-- title:
--   QNorm: val integer le one
-- statement:
--   The QNorm construction uses the val integer le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTwoPlacesOverOfIsSquareLocal.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTwoPlacesOverOfIsSquareLocal.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
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

theorem GlobalTheory.QNorm.val_integer_le_one {E Γ : Type} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation E Γ) (x : 𝓞 E) : u (algebraMap (𝓞 E) E x) ≤ 1 := by sorry
