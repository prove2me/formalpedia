-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_quad_nontrivial
-- name    : GlobalTheory.RegSS.quad_nontrivial
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:11.889963+00:00
-- url     : https://prove2.me/theorems/59084e9d-0d3e-52e7-ac9b-fe8a3b4313fa
-- title:
--   Reg SS: quad nontrivial
-- statement:
--   The Reg SS construction uses the quad nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L492-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L492-L494

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

theorem GlobalTheory.RegSS.quad_nontrivial
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsQuadInvol F E σ) : Nontrivial E := by sorry
