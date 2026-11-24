-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_pIdx_units_of_isAdicComplete
-- name    : GlobalTheory.CNorm.pIdx_units_of_isAdicComplete
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:40.863844+00:00
-- url     : https://prove2.me/theorems/fb90c38f-5330-4464-bb59-9fab8a26de66
-- title:
--   CNorm: p Idx units of is Adic Complete
-- statement:
--   The CNorm construction uses the p Idx units of is Adic Complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowRelIndexUnitsOfIsAdicComplete.lean#L38-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowRelIndexUnitsOfIsAdicComplete.lean#L38-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowImageUnitsCongruentOneModOfIsAdicCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexOneUnitsMulEqCardQuotientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.pIdx_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by sorry
