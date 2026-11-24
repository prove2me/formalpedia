-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGLChar_isClassOn_hcFun
-- name    : GlobalTheory.CompanionTheory.FinGLChar.isClassOn_hcFun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:58:36.160815+00:00
-- url     : https://prove2.me/theorems/7b04756b-3c21-4776-a14d-b386a4e5a5dc
-- title:
--   Fin GLChar: is Class On hc Fun
-- statement:
--   The Fin GLChar construction uses the is Class On hc Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraCharacter.lean#L75-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraCharacter.lean#L75-L88

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

theorem GlobalTheory.CompanionTheory.FinGLChar.isClassOn_hcFun :
    IsClassOn (parab K b) (hcFun b fun c => (lam c).character) := by sorry
