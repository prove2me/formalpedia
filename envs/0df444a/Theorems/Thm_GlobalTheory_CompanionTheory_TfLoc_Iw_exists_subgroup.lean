-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_exists_subgroup
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.exists_subgroup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:28.224343+00:00
-- url     : https://prove2.me/theorems/0c4ee54f-2f99-4858-8bc0-d92a43518311
-- title:
--   Iw: exists subgroup
-- statement:
--   The Iw construction uses the exists subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L91-L96

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
variable {F : Type*} [Field F] [ValuativeRel F] {m : ℕ}

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.exists_subgroup : ∃ U : Subgroup (GL (Fin m) F), (U : Set (GL (Fin m) F)) = iwahori (m := m) F := by sorry
