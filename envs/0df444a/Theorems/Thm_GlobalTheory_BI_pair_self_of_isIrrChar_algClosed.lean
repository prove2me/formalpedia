-- Prove2me | Theorems.Thm_GlobalTheory_BI_pair_self_of_isIrrChar_algClosed
-- name    : GlobalTheory.BI.pair_self_of_isIrrChar_algClosed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:11.305311+00:00
-- url     : https://prove2.me/theorems/d11e9dfe-4f8a-4063-aefd-356c14c57a17
-- title:
--   BI: pair self of is Irr Char alg Closed
-- statement:
--   The BI construction uses the pair self of is Irr Char alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingSelfIrreducibleAlgClos.lean#L6-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingSelfIrreducibleAlgClos.lean#L6-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.pair_self_of_isIrrChar_algClosed (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G]
    (χ : G → L) (h : IsIrrChar L L χ) : pair χ χ = 1 := by sorry
