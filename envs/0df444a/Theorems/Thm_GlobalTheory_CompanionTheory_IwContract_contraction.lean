-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_contraction
-- name    : GlobalTheory.CompanionTheory.IwContract.contraction
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:48:27.566629+00:00
-- url     : https://prove2.me/theorems/f8bc6a14-aa9d-4a53-b2cd-0ae5d6569b06
-- title:
--   Iw Contract: contraction
-- statement:
--   The Iw Contract construction uses the contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L240-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L240-L316

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

theorem GlobalTheory.CompanionTheory.IwContract.contraction {ϖ : Fˣ} (hϖ : IsUniformiser (ϖ : F)) {a : Fin n → ℤ} (ha : StrictlyDominant a)
    (γ : GL (Fin n) F) (hγ : γ ∈ iwDouble F (diagPow ϖ a)) :
    ∃ m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F, ∃ t ∈ torusO F, m⁻¹ * γ * m = diagPow ϖ a * t := by sorry
