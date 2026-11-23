-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_val_det_sub_prod_lt
-- name    : GlobalTheory.CompanionTheory.TwContraction.val_det_sub_prod_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:32.493557+00:00
-- url     : https://prove2.me/theorems/4d011bf5-2252-4525-961a-6e86d5647360
-- title:
--   Tw Contraction: val det sub prod lt
-- statement:
--   The Tw Contraction construction uses the val det sub prod lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L46-L65

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

theorem GlobalTheory.CompanionTheory.TwContraction.val_det_sub_prod_lt (M : Matrix (Fin n) (Fin n) F)
    (h0 : ∀ i l, valuation F (M i l) ≤ 1) (hl : ∀ i l, l < i → valuation F (M i l) < 1) :
    valuation F (M.det - ∏ i, M i i) < 1 := by sorry
