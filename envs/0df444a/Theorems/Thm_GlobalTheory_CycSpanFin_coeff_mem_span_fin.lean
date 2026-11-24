-- Prove2me | Theorems.Thm_GlobalTheory_CycSpanFin_coeff_mem_span_fin
-- name    : GlobalTheory.CycSpanFin.coeff_mem_span_fin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:15.472932+00:00
-- url     : https://prove2.me/theorems/10adaeb5-496e-4ecd-95ff-7a080df6aa5c
-- title:
--   Cyc Span Fin: coeff mem span fin
-- statement:
--   The Cyc Span Fin construction uses the coeff mem span fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAdjoin.lean#L17-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAdjoin.lean#L17-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CycSpanFin
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CycSpanFin.coeff_mem_span_fin {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} {a : ℕ → M} {p : ℂ → M}
    (hp : ∀ u, p u = ∑ i ∈ Finset.range (n + 1), u ^ i • a i) {i : ℕ} (hi : i < n + 1) :
    a i ∈ Submodule.span ℂ (Set.range fun j : Fin (n + 1) => p ((j : ℕ) : ℂ)) := by sorry
