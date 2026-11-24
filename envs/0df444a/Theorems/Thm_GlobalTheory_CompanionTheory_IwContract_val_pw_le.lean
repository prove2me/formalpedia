-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_val_pw_le
-- name    : GlobalTheory.CompanionTheory.IwContract.val_pw_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:51.038041+00:00
-- url     : https://prove2.me/theorems/60c89fe0-1662-4c08-ba0b-d13fe8cee571
-- title:
--   Iw Contract: val pw le
-- statement:
--   The Iw Contract construction uses the val pw le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L85-L91

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

theorem GlobalTheory.CompanionTheory.IwContract.val_pw_le {ϖ : Fˣ} (hϖ : valuation F (ϖ : F) < 1) {a : Fin n → ℤ} (ha : StrictlyDominant a)
    {i j : Fin n} (hij : i < j) :
    valuation F ((ϖ ^ (a i - a j) : Fˣ) : F) ≤ valuation F (ϖ : F) := by sorry
