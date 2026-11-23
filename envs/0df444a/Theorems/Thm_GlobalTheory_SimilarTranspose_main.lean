-- Prove2me | Theorems.Thm_GlobalTheory_SimilarTranspose_main
-- name    : GlobalTheory.SimilarTranspose.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:53.668974+00:00
-- url     : https://prove2.me/theorems/02bbc8fd-78d2-4ea0-8847-2e655b9b3281
-- title:
--   Similar Transpose: main
-- statement:
--   The Similar Transpose construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBilinCyclic.lean#L202-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBilinCyclic.lean#L202-L231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBilinCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SimilarTranspose
open Polynomial

theorem GlobalTheory.SimilarTranspose.main : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k),
    ∃ P : Matrix ι ι k, IsUnit P ∧ P * A = A.transpose * P := by sorry
