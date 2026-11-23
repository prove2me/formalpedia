-- Prove2me | Theorems.Thm_GlobalTheory_det_ne_zero_of_intertwines_of_span_eq_top
-- name    : GlobalTheory.det_ne_zero_of_intertwines_of_span_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:12.7629+00:00
-- url     : https://prove2.me/theorems/85f21763-9bd6-45c7-962a-b17c2a9504db
-- title:
--   Global Theory: det ne zero of intertwines of span eq top
-- statement:
--   The Global Theory construction uses the det ne zero of intertwines of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlIntertwinerOfResidualSpanEqTop.lean#L9-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlIntertwinerOfResidualSpanEqTop.lean#L9-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlIntertwinerOfResidualSpanEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
open Matrix

theorem GlobalTheory.det_ne_zero_of_intertwines_of_span_eq_top {k : Type} [Field k] {G : Type} {r : ℕ}
    (M N : G → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (B : Matrix (Fin r) (Fin r) k) (i j : Fin r) (hB : B i j ≠ 0)
    (h : ∀ g, N g * B = B * M g) : B.det ≠ 0 := by sorry
