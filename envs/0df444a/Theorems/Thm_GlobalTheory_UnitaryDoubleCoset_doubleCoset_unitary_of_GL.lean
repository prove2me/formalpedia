-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_doubleCoset_unitary_of_GL
-- name    : GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:18.806876+00:00
-- url     : https://prove2.me/theorems/bf52273e-abcf-432e-aea2-f8c35d4e9e05
-- title:
--   Unitary Double Coset: double Coset unitary of GL
-- statement:
--   The Unitary Double Coset construction uses the double Coset unitary of GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L243-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC.lean#L243-L278

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

theorem GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (σ : v.adicCompletion K →+* v.adicCompletion K) (n : ℕ) (hσσ : ∀ x, σ (σ x) = x)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hx : ∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) :
    ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)),
    ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)),
    ∀ h ∈ GLint (Fin n) (Ov K v), ∀ k ∈ GLint (Fin n) (Ov K v), g' = h * g * k →
      ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v),
      ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v),
        g' = k₁ * g * k₂ := by sorry
