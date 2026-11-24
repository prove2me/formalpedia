-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_colGeSplit_bijective
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.colGeSplit_bijective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:12.545831+00:00
-- url     : https://prove2.me/theorems/dc0ffe2e-3d9d-4d56-91cc-73551849ea56
-- title:
--   Col Step: col Ge Split bijective
-- statement:
--   The Col Step construction uses the col Ge Split bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternSetCardColumnStep.lean#L25-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternSetCardColumnStep.lean#L25-L54

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.colGeSplit_bijective (d j : ℕ) (hj : j < d) : Function.Bijective (colGeSplit d j hj) := by sorry
