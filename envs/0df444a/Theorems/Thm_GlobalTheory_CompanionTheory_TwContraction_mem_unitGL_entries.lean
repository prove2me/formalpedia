-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_mem_unitGL_entries
-- name    : GlobalTheory.CompanionTheory.TwContraction.mem_unitGL_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:28.392717+00:00
-- url     : https://prove2.me/theorems/b86c1d3f-8e0e-4d4e-a0e7-60cb5ecf6e8f
-- title:
--   Tw Contraction: mem unit GL entries
-- statement:
--   The Tw Contraction construction uses the mem unit GL entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L67-L70

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

theorem GlobalTheory.CompanionTheory.TwContraction.mem_unitGL_entries {g : GL (Fin n) F} (hg : g ∈ unitGL (n := Fin n) F) (i l : Fin n) :
    valuation F ((g : Matrix (Fin n) (Fin n) F) i l) ≤ 1 := by sorry
