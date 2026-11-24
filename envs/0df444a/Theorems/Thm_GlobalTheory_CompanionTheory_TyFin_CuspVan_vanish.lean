-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_vanish
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspVan.vanish
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:43.023478+00:00
-- url     : https://prove2.me/theorems/6947b1ee-ab20-4176-8488-98bdc187f8d6
-- title:
--   Cusp Van: vanish
-- statement:
--   The Cusp Van construction uses the vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L172-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L172-L224

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

theorem GlobalTheory.CompanionTheory.TyFin.CuspVan.vanish {s s' : ℕ} (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hcusp : ∀ c, IsCuspidal K (lam c))
    (c : Fin s) (i₀ j₀ : ι) (hi : b i₀ = c) (hj : b j₀ = c) (hβ : β i₀ ≠ β j₀)
    (H : Subgroup (GL ι K)) [DecidablePred (· ∈ H)] (F : GL ι K → ℂ) (hH : H ≤ parab K b)
    (hF : ∀ u ∈ unip K β, (∀ i j, b i ≠ b j → (u : Matrix ι ι K) i j = 0) →
      u ∈ H ∧ ∀ h ∈ H, F (h * u) = F h) :
    ∑ h, (if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0 := by sorry
