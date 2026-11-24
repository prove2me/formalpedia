-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_pmFacts
-- name    : GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:38.721082+00:00
-- url     : https://prove2.me/theorems/7ed0c42e-5d93-4a17-ad99-66c151f8f03b
-- title:
--   Pm: pm Facts
-- statement:
--   The Pm construction uses the pm Facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L85-L91

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Pm
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts : ReciprocityTheory.Ty.Fin.St.PmFacts := by sorry
