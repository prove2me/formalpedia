-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_exists_equiv_factors
-- name    : GlobalTheory.CompanionTheory.TyFin.Mirrors.exists_equiv_factors
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:32.33681+00:00
-- url     : https://prove2.me/theorems/9fc74b0b-648b-4e1f-9efe-dd416afbd30c
-- title:
--   Mirrors: exists equiv factors
-- statement:
--   The Mirrors construction uses the exists equiv factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirrorPartitions.lean#L168-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MirrorPartitions.lean#L168-L180

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin PI.GreenLabelSurjWork
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Mirrors
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

theorem GlobalTheory.CompanionTheory.TyFin.Mirrors.exists_equiv_factors {s s' : ℕ} {P : Fin s → K[X]} {P' : Fin s' → K[X]}
    (hi : ∀ c, Irreducible (P c)) (hm : ∀ c, (P c).Monic) (hi' : ∀ c, Irreducible (P' c))
    (hm' : ∀ c, (P' c).Monic) (hj : Function.Injective P) (hj' : Function.Injective P')
    (h : ∏ c, P c = ∏ c, P' c) : ∃ π : Fin s ≃ Fin s', ∀ c, P' (π c) = P c := by sorry
