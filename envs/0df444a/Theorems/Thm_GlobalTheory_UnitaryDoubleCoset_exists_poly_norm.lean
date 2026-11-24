-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_exists_poly_norm
-- name    : GlobalTheory.UnitaryDoubleCoset.exists_poly_norm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:46:40.722394+00:00
-- url     : https://prove2.me/theorems/e4a9d7d9-a79f-4d45-9c3d-b60f21f31a2d
-- title:
--   Unitary Double Coset: exists poly norm
-- statement:
--   The Unitary Double Coset construction uses the exists poly norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L103-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L103-L120

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

theorem GlobalTheory.UnitaryDoubleCoset.exists_poly_norm {c : O →+* O} (hc : ∀ x, c (c x) = x)
    (hN : ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) →
      ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X)
    {B : Matrix n n O} (hB : _root_.Formalism.UG.cT c B = B) (hu : IsUnit B) :
    ∃ p : Polynomial O, _root_.Formalism.UG.cT c (Polynomial.aeval B p) * Polynomial.aeval B p = B := by sorry
