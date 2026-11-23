-- Prove2me | Theorems.Thm_GlobalTheory_T_idelicRingClassLattice_one_eq_order
-- name    : GlobalTheory.T.idelicRingClassLattice_one_eq_order
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:18.973824+00:00
-- url     : https://prove2.me/theorems/05712cb0-db2b-4234-8128-4fbd19cd58b8
-- title:
--   T: idelic Ring Class Lattice one eq order
-- statement:
--   The T construction uses the idelic Ring Class Lattice one eq order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdelicRingClassLatticeOneEqOrderStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdelicRingClassLatticeOneEqOrderStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrder
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrderStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.idelicRingClassLattice_one_eq_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by sorry
