-- Prove2me | Theorems.Thm_GlobalTheory_SimilarTranspose_exists_bilin_cyclic
-- name    : GlobalTheory.SimilarTranspose.exists_bilin_cyclic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:23.48053+00:00
-- url     : https://prove2.me/theorems/75e55df1-fc1d-4bb2-86fc-68192c558e22
-- title:
--   Similar Transpose: exists bilin cyclic
-- statement:
--   The Similar Transpose construction uses the exists bilin cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBilinCyclic.lean#L48-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBilinCyclic.lean#L48-L67

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

theorem GlobalTheory.SimilarTranspose.exists_bilin_cyclic {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ B : (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] k,
      (∀ x y, B ((X : k[X]) • x) y = B x ((X : k[X]) • y)) ∧ ∀ y, (∀ x, B x y = 0) → y = 0 := by sorry
