-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_along_of_along
-- name    : GlobalTheory.CompanionTheory.TyFin.IpIso.along_of_along
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:55.635939+00:00
-- url     : https://prove2.me/theorems/e27b86d8-a40c-462f-8f71-2c658136956b
-- title:
--   Ip Iso: along of along
-- statement:
--   The Ip Iso construction uses the along of along property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIso.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIso.lean#L35-L47

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
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
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.IpIso
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem GlobalTheory.CompanionTheory.TyFin.IpIso.along_of_along (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e e' : α ≃ β)
    (φ : lam ≃ₗ[ℂ] mu) (h : ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e' g) (φ x)) :
    ∃ ψ : lam ≃ₗ[ℂ] mu, ∀ g x, ψ (lam.ρ g x) = mu.ρ (glEquiv K e g) (ψ x) := by sorry
