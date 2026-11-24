-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_apply
-- name    : GlobalTheory.CompanionTheory.TyFin.Maschke.avg_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:59.225431+00:00
-- url     : https://prove2.me/theorems/e22d687f-5ea9-4dc8-9fe5-162476ec556d
-- title:
--   Maschke: avg apply
-- statement:
--   The Maschke construction uses the avg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L22-L24

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Maschke
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem GlobalTheory.CompanionTheory.TyFin.Maschke.avg_apply (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) (v : V) :
    avg ρ σ f v = (Fintype.card Γ : ℂ)⁻¹ • ∑ g : Γ, σ g (f (ρ g⁻¹ v)) := by sorry
