-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_exists_mem_iwahori
-- name    : GlobalTheory.CompanionTheory.IwContract.exists_mem_iwahori
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:48:18.574133+00:00
-- url     : https://prove2.me/theorems/e0ce859a-3b4b-4732-9c79-0a9a34381c96
-- title:
--   Iw Contract: exists mem iwahori
-- statement:
--   The Iw Contract construction uses the exists mem iwahori property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L50-L66

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem GlobalTheory.CompanionTheory.IwContract.exists_mem_iwahori (M : Matrix (Fin n) (Fin n) F) (h1 : ∀ i j, valuation F (M i j) ≤ 1)
    (h2 : ∀ i j, j < i → valuation F (M i j) < 1) (h3 : ∀ i, valuation F (M i i) = 1) :
    ∃ g ∈ GlobalTheory.SmGL.iwahori F (Fin n), g.val = M := by sorry
