-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_hasFixed_le
-- name    : GlobalTheory.CompanionTheory.TyFinJacquet.hasFixed_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:41.031708+00:00
-- url     : https://prove2.me/theorems/160df46e-f540-484d-bab3-1eea0cf4080e
-- title:
--   Ty Fin Jacquet: has Fixed le
-- statement:
--   The Ty Fin Jacquet construction uses the has Fixed le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L162-L164

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

theorem GlobalTheory.CompanionTheory.TyFinJacquet.hasFixed_le {τ : FDRep ℂ (GL ι K)} {s : ℕ} (h : HasFixed τ s) : s ≤ Fintype.card ι := by sorry
