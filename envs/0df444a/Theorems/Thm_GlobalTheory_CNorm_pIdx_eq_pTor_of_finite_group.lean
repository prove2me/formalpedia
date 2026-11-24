-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_pIdx_eq_pTor_of_finite_group
-- name    : GlobalTheory.CNorm.pIdx_eq_pTor_of_finite_group
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:43.802805+00:00
-- url     : https://prove2.me/theorems/eb9664fd-39e6-4043-9979-217770817f13
-- title:
--   CNorm: p Idx eq p Tor of finite group
-- statement:
--   The CNorm construction uses the p Idx eq p Tor of finite group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowRelIndexUnitsOfIsAdicComplete.lean#L11-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowRelIndexUnitsOfIsAdicComplete.lean#L11-L36

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

theorem GlobalTheory.CNorm.pIdx_eq_pTor_of_finite_group (p : ℕ) {G : Type} [CommGroup G] [Finite G]
    (U : Subgroup G) : pTor p U ≠ 0 ∧ pIdx p U = pTor p U := by sorry
