-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_repIso_of_constituent
-- name    : GlobalTheory.CompanionTheory.TyFin.FromMackey.repIso_of_constituent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:13.083257+00:00
-- url     : https://prove2.me/theorems/cf0e443f-f0d2-448a-8d3a-a359234138fa
-- title:
--   From Mackey: rep Iso of constituent
-- statement:
--   The From Mackey construction uses the rep Iso of constituent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L18-L27

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.FromMackey
variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem GlobalTheory.CompanionTheory.TyFin.FromMackey.repIso_of_constituent {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : FDRep ℂ Γ) (ρ : Representation ℂ Γ V) (hτ : Simple τ) (hρ : IsIrr ρ)
    (hc : IsConstituent τ ρ) : RepIso τ.ρ ρ := by sorry
