-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspIff_mem_stdRadical
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspIff.mem_stdRadical
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:03.015109+00:00
-- url     : https://prove2.me/theorems/c3de28c8-9494-485c-9299-51968f6eaa5c
-- title:
--   Cusp Iff: mem std Radical
-- statement:
--   The Cusp Iff construction uses the mem std Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalOfUnipotentSumsVanish.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalOfUnipotentSumsVanish.lean#L53-L55

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanish
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
open Polynomial CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspIff

theorem GlobalTheory.CompanionTheory.TyFin.CuspIff.mem_stdRadical {K : Type} [Field K] [Fintype K] [DecidableEq K] {d a : ℕ} {u : GL (Fin d) K} :
    u ∈ stdRadical K d a ↔ ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by sorry
