-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_cT_cT
-- name    : GlobalTheory.UnitaryDoubleCoset.cT_cT
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:42:54.583101+00:00
-- url     : https://prove2.me/theorems/d2c20e47-6fe8-49ac-a186-0156d651932e
-- title:
--   Unitary Double Coset: c T c T
-- statement:
--   The Unitary Double Coset construction uses the c T c T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L70-L73

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitaryDoubleCoset
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
open IsDedekindDomain NumberField
open scoped TensorProduct Matrix
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n]

theorem GlobalTheory.UnitaryDoubleCoset.cT_cT {c : O →+* O} (hc : ∀ x, c (c x) = x)
    (M : Matrix n n O) : _root_.Formalism.UG.cT c (_root_.Formalism.UG.cT c M) = M := by sorry
