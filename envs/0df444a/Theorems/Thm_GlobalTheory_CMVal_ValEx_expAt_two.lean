-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_expAt_two
-- name    : GlobalTheory.CMVal.ValEx.expAt_two
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:26.494802+00:00
-- url     : https://prove2.me/theorems/2d987036-753a-43f2-af74-5f9ede238483
-- title:
--   Val Ex: exp At two
-- statement:
--   The Val Ex construction uses the exp At two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L413-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L413-L417

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.ValEx.expAt_two {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} (h2 : LevelLe χ P 2) (h1 : ¬ LevelLe χ P 1) : ExpAt χ P 2 := by sorry
