-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_cT_map
-- name    : GlobalTheory.UnitaryDoubleCoset.cT_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:49.84538+00:00
-- url     : https://prove2.me/theorems/1d3a6742-b70c-475e-889d-ba56dc4f3f7a
-- title:
--   Unitary Double Coset: c T map
-- statement:
--   The Unitary Double Coset construction uses the c T map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L60-L64

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_cT_map

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

theorem GlobalTheory.UnitaryDoubleCoset.cT_map (ι : O →+* L) {c : O →+* O} {σ : L →+* L}
    (hι : ∀ x, σ (ι x) = ι (c x)) (M : Matrix n n O) :
    _root_.Formalism.UG.cT σ (M.map ι) = (_root_.Formalism.UG.cT c M).map ι := by sorry
