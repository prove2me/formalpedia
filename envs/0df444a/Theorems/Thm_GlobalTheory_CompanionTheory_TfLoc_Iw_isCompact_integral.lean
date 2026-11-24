-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_isCompact_integral
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.isCompact_integral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:56.277808+00:00
-- url     : https://prove2.me/theorems/8962d565-3787-45b1-8aaa-2a83d6da982f
-- title:
--   Iw: is Compact integral
-- statement:
--   The Iw construction uses the is Compact integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L159-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L159-L170

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

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.isCompact_integral : IsCompact {M : Matrix (Fin m) (Fin m) F | ∀ i j, valuation F (M i j) ≤ 1} := by sorry
