-- Prove2me | Theorems.Thm_GlobalTheory_multiset_newton_psum
-- name    : GlobalTheory.multiset_newton_psum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:15.482315+00:00
-- url     : https://prove2.me/theorems/b466e999-a31f-4ead-b89c-21334bac9db8
-- title:
--   Global Theory: multiset newton psum
-- statement:
--   The Global Theory construction uses the multiset newton psum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MultisetPowerSumNewtonIdentity.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MultisetPowerSumNewtonIdentity.lean#L28-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MultisetPowerSumNewtonIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory

theorem GlobalTheory.multiset_newton_psum (s : Multiset ℂ) (r : ℕ) (hr : 0 < r) :
    (s.map (· ^ r)).sum = (-1) ^ (r + 1) * (r : ℂ) * s.esymm r
      - ∑ i ∈ Finset.Ioo 0 r, (-1) ^ i * s.esymm i * (s.map (· ^ (r - i))).sum := by sorry
