-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_val_aut_le_one
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.val_aut_le_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:35.851795+00:00
-- url     : https://prove2.me/theorems/dd413aa9-738e-4dc6-9b9e-ced5c04529f4
-- title:
--   Iw: val aut le one
-- statement:
--   The Iw construction uses the val aut le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L210-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L210-L214

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.val_aut_le_one (τ : E ≃ₐ[k] E) {x : E} (hx : valuation E x ≤ 1) :
    valuation E (τ x) ≤ 1 := by sorry
