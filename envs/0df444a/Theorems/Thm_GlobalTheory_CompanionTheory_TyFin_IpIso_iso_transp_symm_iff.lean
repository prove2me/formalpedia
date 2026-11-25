-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_iso_transp_symm_iff
-- name    : GlobalTheory.CompanionTheory.TyFin.IpIso.iso_transp_symm_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:04.139314+00:00
-- url     : https://prove2.me/theorems/2c06e27a-ebed-4274-a120-5c157b38ff30
-- title:
--   Ip Iso: iso transp symm iff
-- statement:
--   The Ip Iso construction uses the iso transp symm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIso.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIso.lean#L58-L71

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

theorem GlobalTheory.CompanionTheory.TyFin.IpIso.iso_transp_symm_iff (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β) :
    Nonempty (lam ≅ transp e.symm mu) ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by sorry
