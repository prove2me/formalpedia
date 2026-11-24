-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGLChar_trace_infl
-- name    : GlobalTheory.CompanionTheory.FinGLChar.trace_infl
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:58:36.668835+00:00
-- url     : https://prove2.me/theorems/4921eaed-ad31-41e1-b1b4-808bab83c4a9
-- title:
--   Fin GLChar: trace infl
-- statement:
--   The Fin GLChar construction uses the trace infl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraCharacter.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraCharacter.lean#L26-L33

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGLChar
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

theorem GlobalTheory.CompanionTheory.FinGLChar.trace_infl (p : parab K b) :
    LinearMap.trace ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) (infl K b lam p) =
      hcFun b (fun c => (lam c).character) p.1 := by sorry
