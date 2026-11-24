-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_val_det_of_mem_unitGL
-- name    : GlobalTheory.CompanionTheory.TwContraction.val_det_of_mem_unitGL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:49.689521+00:00
-- url     : https://prove2.me/theorems/2d9e6755-6cdc-4126-9b74-00a4a39dc9d1
-- title:
--   Tw Contraction: val det of mem unit GL
-- statement:
--   The Tw Contraction construction uses the val det of mem unit GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L72-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L72-L96

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

theorem GlobalTheory.CompanionTheory.TwContraction.val_det_of_mem_unitGL {g : GL (Fin n) F} (hg : g ∈ unitGL (n := Fin n) F) :
    valuation F (g : Matrix (Fin n) (Fin n) F).det = 1 := by sorry
