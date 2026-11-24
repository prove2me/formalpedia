-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_TermUnit_prod_norm_sq
-- name    : GlobalTheory.CMVal.TermUnit.prod_norm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:11.231184+00:00
-- url     : https://prove2.me/theorems/cd747691-050a-4b15-b798-59b9e250ca6a
-- title:
--   Term Unit: prod norm sq
-- statement:
--   The Term Unit construction uses the prod norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdNormSq.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdNormSq.lean#L30-L35

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.CMVal.TermUnit.prod_norm_sq [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |(Algebra.norm ℚ x : ℝ)| := by sorry
