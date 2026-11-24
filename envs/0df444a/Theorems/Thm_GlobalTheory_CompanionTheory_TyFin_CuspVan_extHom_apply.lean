-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_extHom_apply
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:38.71172+00:00
-- url     : https://prove2.me/theorems/bf052b5f-9196-44d8-aeb7-2273dc092f6d
-- title:
--   Cusp Van: ext Hom apply
-- statement:
--   The Cusp Van construction uses the ext Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L100-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L100-L113

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

theorem GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_apply {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K) (i j : ι) :
    (extHom b c v : Matrix ι ι K) i j =
      if h : b i = c ∧ b j = c then (v : Matrix {i // b i = c} {i // b i = c} K) ⟨i, h.1⟩ ⟨j, h.2⟩ else if i = j then 1 else 0 := by sorry
