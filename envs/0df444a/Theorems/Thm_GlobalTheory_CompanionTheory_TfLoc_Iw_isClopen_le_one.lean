-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_isClopen_le_one
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.isClopen_le_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:53.9628+00:00
-- url     : https://prove2.me/theorems/dfe5d785-01e9-4867-89c6-a6eb6d7bcfbb
-- title:
--   Iw: is Clopen le one
-- statement:
--   The Iw construction uses the is Clopen le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L118-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L118-L128

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

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.isClopen_le_one : IsClopen {x : F | valuation F x ≤ 1} := by sorry
