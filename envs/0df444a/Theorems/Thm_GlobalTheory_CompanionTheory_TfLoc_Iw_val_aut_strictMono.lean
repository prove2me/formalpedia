-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_val_aut_strictMono
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.val_aut_strictMono
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:29.316356+00:00
-- url     : https://prove2.me/theorems/3452c886-4b99-4088-b567-9203c6ad51e3
-- title:
--   Iw: val aut strict Mono
-- statement:
--   The Iw construction uses the val aut strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L216-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L216-L238

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

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.val_aut_strictMono (τ : E ≃ₐ[k] E) {a b : E} (h : valuation E a < valuation E b) :
    valuation E (τ a) < valuation E (τ b) := by sorry
