-- Prove2me | Theorems.Thm_GlobalTheory_SimilarTranspose_exists_bilin
-- name    : GlobalTheory.SimilarTranspose.exists_bilin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:21.272085+00:00
-- url     : https://prove2.me/theorems/8933ae8b-e638-430c-8462-72a789138e58
-- title:
--   Similar Transpose: exists bilin
-- statement:
--   The Similar Transpose construction uses the exists bilin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBilinCyclic.lean#L69-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBilinCyclic.lean#L69-L102

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

theorem GlobalTheory.SimilarTranspose.exists_bilin {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : W →ₗ[k] W) :
    ∃ B : W →ₗ[k] W →ₗ[k] k, (∀ x y, B (T x) y = B x (T y)) ∧ ∀ y, (∀ x, B x y = 0) → y = 0 := by sorry
