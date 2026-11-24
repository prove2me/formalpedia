-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_isClosed_val_le_pow
-- name    : GlobalTheory.CompanionTheory.IwContract.isClosed_val_le_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:48:22.66933+00:00
-- url     : https://prove2.me/theorems/12554a20-b3a9-4b2e-86e6-394b46182ab2
-- title:
--   Iw Contract: is Closed val le pow
-- statement:
--   The Iw Contract construction uses the is Closed val le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L68-L80

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

theorem GlobalTheory.CompanionTheory.IwContract.isClosed_val_le_pow (ϖ : Fˣ) (k : ℕ) :
    IsClosed {y : F | valuation F y ≤ valuation F (ϖ : F) ^ k} := by sorry
