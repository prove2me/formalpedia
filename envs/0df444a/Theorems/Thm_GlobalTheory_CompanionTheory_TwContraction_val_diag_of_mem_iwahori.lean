-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_val_diag_of_mem_iwahori
-- name    : GlobalTheory.CompanionTheory.TwContraction.val_diag_of_mem_iwahori
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:10.356537+00:00
-- url     : https://prove2.me/theorems/f625e52e-bdc1-42b0-854e-f7e6b0618973
-- title:
--   Tw Contraction: val diag of mem iwahori
-- statement:
--   The Tw Contraction construction uses the val diag of mem iwahori property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L121-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L121-L131

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}

theorem GlobalTheory.CompanionTheory.TwContraction.val_diag_of_mem_iwahori {c : GL (Fin n) F} (hc : c ∈ iwahori (m := n) F) (i : Fin n) :
    valuation F ((c : Matrix (Fin n) (Fin n) F) i i) = 1 := by sorry
