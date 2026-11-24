-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_equivariant_tprod
-- name    : GlobalTheory.CompanionTheory.TyFinJacquet.equivariant_tprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:55.83528+00:00
-- url     : https://prove2.me/theorems/c285ff87-1b6f-45d3-8dd5-6a03cfc31127
-- title:
--   Ty Fin Jacquet: equivariant tprod
-- statement:
--   The Ty Fin Jacquet construction uses the equivariant tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L271-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JacquetModuleAll.lean#L271-L275

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

theorem GlobalTheory.CompanionTheory.TyFinJacquet.equivariant_tprod (heq : ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) (p : parab K b)
    (f : ∀ c, (lam c : Type)) :
    Φ (PiTensorProduct.tprod ℂ fun c => (lam c).ρ (levi K b c p) (f c)) = τ.ρ p.1 (Φ (PiTensorProduct.tprod ℂ f)) := by sorry
