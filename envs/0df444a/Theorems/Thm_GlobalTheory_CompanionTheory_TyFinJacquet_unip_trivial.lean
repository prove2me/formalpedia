-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_unip_trivial
-- name    : GlobalTheory.CompanionTheory.TyFinJacquet.unip_trivial
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:26.169809+00:00
-- url     : https://prove2.me/theorems/0a973c7d-82a3-4204-9df6-f05af7721d97
-- title:
--   Ty Fin Jacquet: unip trivial
-- statement:
--   The Ty Fin Jacquet construction uses the unip trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L145-L149

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinJacquet
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem GlobalTheory.CompanionTheory.TyFinJacquet.unip_trivial (b : ι → Fin s) (hb : ∀ i j, b i = b j) {u : GL ι K} (hu : u ∈ unip K b) : u = 1 := by sorry
