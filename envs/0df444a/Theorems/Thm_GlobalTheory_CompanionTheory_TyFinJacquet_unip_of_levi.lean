-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_unip_of_levi
-- name    : GlobalTheory.CompanionTheory.TyFinJacquet.unip_of_levi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:45.623971+00:00
-- url     : https://prove2.me/theorems/c8c8b305-0d46-43b8-9835-2d1ad6e66409
-- title:
--   Ty Fin Jacquet: unip of levi
-- statement:
--   The Ty Fin Jacquet construction uses the unip of levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L104-L108

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

theorem GlobalTheory.CompanionTheory.TyFinJacquet.unip_of_levi (b : ι → Fin s) (p : parab K b) : (dGL b (leviHom b p))⁻¹ * p.1 ∈ unip K b := by sorry
