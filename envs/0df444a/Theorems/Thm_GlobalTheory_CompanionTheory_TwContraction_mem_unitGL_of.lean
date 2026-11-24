-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_mem_unitGL_of
-- name    : GlobalTheory.CompanionTheory.TwContraction.mem_unitGL_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:54.1437+00:00
-- url     : https://prove2.me/theorems/409e2d30-7467-4c70-b218-a6b7ce972f85
-- title:
--   Tw Contraction: mem unit GL of
-- statement:
--   The Tw Contraction construction uses the mem unit GL of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L98-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L98-L119

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

theorem GlobalTheory.CompanionTheory.TwContraction.mem_unitGL_of (g : GL (Fin n) F) (h0 : ∀ i l, valuation F ((g : Matrix (Fin n) (Fin n) F) i l) ≤ 1)
    (hd : valuation F (g : Matrix (Fin n) (Fin n) F).det = 1) : g ∈ unitGL (n := Fin n) F := by sorry
