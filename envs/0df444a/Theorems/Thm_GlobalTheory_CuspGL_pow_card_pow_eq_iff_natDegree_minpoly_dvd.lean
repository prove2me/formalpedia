-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_pow_card_pow_eq_iff_natDegree_minpoly_dvd
-- name    : GlobalTheory.CuspGL.pow_card_pow_eq_iff_natDegree_minpoly_dvd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:33:11.705078+00:00
-- url     : https://prove2.me/theorems/93b0fbb1-cf27-4787-823c-6c92c91ac890
-- title:
--   Cusp GL: pow card pow eq iff nat Degree minpoly dvd
-- statement:
--   The Cusp GL construction uses the pow card pow eq iff nat Degree minpoly dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RegularIffNatDegreeAndExistsEllipticGL.lean#L8-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RegularIffNatDegreeAndExistsEllipticGL.lean#L8-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.pow_card_pow_eq_iff_natDegree_minpoly_dvd (F : Type) [Field F] [Finite F]
    (α : AlgebraicClosure F) (e : ℕ) :
    α ^ Nat.card F ^ e = α ↔ (minpoly F α).natDegree ∣ e := by sorry
