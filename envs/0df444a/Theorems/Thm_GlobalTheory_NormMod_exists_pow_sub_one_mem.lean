-- Prove2me | Theorems.Thm_GlobalTheory_NormMod_exists_pow_sub_one_mem
-- name    : GlobalTheory.NormMod.exists_pow_sub_one_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:55.626549+00:00
-- url     : https://prove2.me/theorems/4d69b9a8-d6bf-4656-a391-d760372baf06
-- title:
--   Norm Mod: exists pow sub one mem
-- statement:
--   The Norm Mod construction uses the exists pow sub one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsHostNormModCoprimeLevelHalf.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsHostNormModCoprimeLevelHalf.lean#L78-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
variable {R : Type*} [CommRing R] [Finite R]

theorem GlobalTheory.NormMod.exists_pow_sub_one_mem (a : R) :
    ∃ k, 0 < k ∧ ∀ P : Ideal R, P.IsPrime → a ∉ P → a ^ k - 1 ∈ P := by sorry
