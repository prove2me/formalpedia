-- Prove2me | Theorems.Thm_GlobalTheory_SimilarTranspose_exists_form
-- name    : GlobalTheory.SimilarTranspose.exists_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:45:55.880027+00:00
-- url     : https://prove2.me/theorems/a7614ed1-1fb7-4fe0-a9af-ad049e260cc9
-- title:
--   Similar Transpose: exists form
-- statement:
--   The Similar Transpose construction uses the exists form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBilinCyclic.lean#L9-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBilinCyclic.lean#L9-L46

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

theorem GlobalTheory.SimilarTranspose.exists_form {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ l : k[X] →ₗ[k] k, (∀ a, f ∣ a → l a = 0) ∧ ∀ a, (∀ b, l (a * b) = 0) → f ∣ a := by sorry
