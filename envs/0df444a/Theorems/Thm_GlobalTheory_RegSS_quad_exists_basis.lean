-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_quad_exists_basis
-- name    : GlobalTheory.RegSS.quad_exists_basis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:08.801841+00:00
-- url     : https://prove2.me/theorems/cf5d0485-ec5b-4301-a0da-553189c3c214
-- title:
--   Reg SS: quad exists basis
-- statement:
--   The Reg SS construction uses the quad exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L500-L554
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L500-L554

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}

theorem GlobalTheory.RegSS.quad_exists_basis [CharZero F]
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsQuadInvol F E σ) :
    ∃ (b : Module.Basis (Fin 2) F E) (d : F), b 0 = 1 ∧ σ (b 1) = - b 1 ∧ d ≠ 0 ∧
      b 1 * b 1 = algebraMap F E d := by sorry
