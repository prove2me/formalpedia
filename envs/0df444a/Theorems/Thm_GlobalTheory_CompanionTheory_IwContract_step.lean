-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_step
-- name    : GlobalTheory.CompanionTheory.IwContract.step
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:53.879815+00:00
-- url     : https://prove2.me/theorems/2f71f27e-ad7e-49b8-8d49-dcde3da88eaa
-- title:
--   Iw Contract: step
-- statement:
--   The Iw Contract construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L93-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriContraction.lean#L93-L238

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

theorem GlobalTheory.CompanionTheory.IwContract.step {ϖ : Fˣ} (hϖ : IsUniformiser (ϖ : F)) {a : Fin n → ℤ} (ha : StrictlyDominant a)
    {r : ValueGroupWithZero F} {c : GL (Fin n) F} (hc : Near r c) :
    ∃ m ∈ GlobalTheory.SmGL.iwahori F (Fin n), ∃ c' : GL (Fin n) F, Near (r * valuation F (ϖ : F)) c' ∧
      (diagPow ϖ a * c) * m = m * (diagPow ϖ a * c') := by sorry
