-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_pow_natDegree_ne_one
-- name    : GlobalTheory.CuspGL.LogDeriv.pow_natDegree_ne_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:22.554342+00:00
-- url     : https://prove2.me/theorems/ff1f7c5d-f25e-4c6d-bcc1-4f21908c996b
-- title:
--   Log Deriv: pow nat Degree ne one
-- statement:
--   The Log Deriv construction uses the pow nat Degree ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveMulEqVonMangoldtConvolution.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveMulEqVonMangoldtConvolution.lean#L46-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveMulEqVonMangoldtConvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.LogDeriv
variable {F : Type} [Field F]

theorem GlobalTheory.CuspGL.LogDeriv.pow_natDegree_ne_one {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : n ≠ 0) : (q : ℂ) ^ n - 1 ≠ 0 := by sorry
