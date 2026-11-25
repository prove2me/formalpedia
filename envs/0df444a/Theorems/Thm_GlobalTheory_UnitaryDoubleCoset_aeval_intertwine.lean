-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_aeval_intertwine
-- name    : GlobalTheory.UnitaryDoubleCoset.aeval_intertwine
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:47.749012+00:00
-- url     : https://prove2.me/theorems/f7f8493b-74c8-4fc8-b90f-11268bc4c010
-- title:
--   Unitary Double Coset: aeval intertwine
-- statement:
--   The Unitary Double Coset construction uses the aeval intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L36-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L36-L54

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

theorem GlobalTheory.UnitaryDoubleCoset.aeval_intertwine (ι : O →+* L) {B B' : Matrix n n O} {g : Matrix n n L}
    (h : B.map ι * g = g * B'.map ι) (p : Polynomial O) :
    (Polynomial.aeval B p).map ι * g = g * (Polynomial.aeval B' p).map ι := by sorry
