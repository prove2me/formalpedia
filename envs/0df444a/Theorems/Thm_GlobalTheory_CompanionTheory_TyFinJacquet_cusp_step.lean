-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_cusp_step
-- name    : GlobalTheory.CompanionTheory.TyFinJacquet.cusp_step
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:44.539106+00:00
-- url     : https://prove2.me/theorems/ad97b041-0d97-49d8-aea8-201cad663be6
-- title:
--   Ty Fin Jacquet: cusp step
-- statement:
--   The Ty Fin Jacquet construction uses the cusp step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L318-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L318-L341

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
variable {τ : FDRep ℂ (GL ι K)} {b : ι → Fin s} {lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)}
  {Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ}

theorem GlobalTheory.CompanionTheory.TyFinJacquet.cusp_step (hb : Function.Surjective b) (hΦ : Φ ≠ 0)
    (heq : ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) (c : Fin s) (hirr : IsIrr (lam c).ρ)
    {t : ℕ} (ht : 1 ≤ t) (b₁ : {i // b i = c} → Fin t) (hb₁ : Function.Surjective b₁)
    (v : lam c) (hv : v ≠ 0) (hfix : ∀ u ∈ unip K b₁, (lam c).ρ u v = v) : HasFixed τ (s + t - 1) := by sorry
