-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGLChar_mul_mul_eq_iff
-- name    : GlobalTheory.CompanionTheory.FinGLChar.mul_mul_eq_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:58:28.611864+00:00
-- url     : https://prove2.me/theorems/2e0abfc6-5947-4acb-a2b0-06fb1d5e3a1d
-- title:
--   Fin GLChar: mul mul eq iff
-- statement:
--   The Fin GLChar construction uses the mul mul eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraCharacter.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraCharacter.lean#L12-L21

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

theorem GlobalTheory.CompanionTheory.FinGLChar.mul_mul_eq_iff {G : Type} [Group G] (a x g : G) :
    a * (x * g) = x ↔ a⁻¹ = x * g * x⁻¹ := by sorry
