-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_continuous_inv_entry
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.continuous_inv_entry
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:32.39713+00:00
-- url     : https://prove2.me/theorems/7bd551c7-1d41-40a8-aa19-fcbfdd808df2
-- title:
--   Iw: continuous inv entry
-- statement:
--   The Iw construction uses the continuous inv entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L134-L136

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.continuous_inv_entry (i j : Fin m) :
    Continuous fun g : GL (Fin m) F => ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j := by sorry
