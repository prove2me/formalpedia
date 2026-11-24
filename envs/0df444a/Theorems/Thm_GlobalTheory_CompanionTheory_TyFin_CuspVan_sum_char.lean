-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_sum_char
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspVan.sum_char
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:17.429799+00:00
-- url     : https://prove2.me/theorems/08a77d3d-57de-41d2-9597-aaa89bd36381
-- title:
--   Cusp Van: sum char
-- statement:
--   The Cusp Van construction uses the sum char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L64-L71

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspVan
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open Classical

theorem GlobalTheory.CompanionTheory.TyFin.CuspVan.sum_char {t : ℕ} (bb : ι → Fin t) (hs : Function.Surjective bb) (ht : 2 ≤ t)
    (τ : FDRep ℂ (GL ι K)) (hτ : IsCuspidal K τ) (g : GL ι K) :
    ∑ v ∈ Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb), τ.character (g * v) = 0 := by sorry
