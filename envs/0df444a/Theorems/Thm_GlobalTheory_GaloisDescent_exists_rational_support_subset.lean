-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_exists_rational_support_subset
-- name    : GlobalTheory.GaloisDescent.exists_rational_support_subset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:35.614143+00:00
-- url     : https://prove2.me/theorems/773b0ba4-d53a-40a7-807f-096dcdd003ff
-- title:
--   Galois Descent: exists rational support subset
-- statement:
--   The Galois Descent construction uses the exists rational support subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L24-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L24-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L M G ι : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module L M]

theorem GlobalTheory.GaloisDescent.exists_rational_support_subset (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (b : Basis ι L M) (φ : G → M →+ M) (hφ : ∀ g a i, φ g (a • b i) = s g a • b i)
    (W : Submodule L M) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) (w : M) (hw : w ∈ W) (h0 : w ≠ 0) :
    ∃ u ∈ W, (∀ i, b.repr u i ∈ Set.range (algebraMap K L)) ∧
      (b.repr u).support ⊆ (b.repr w).support ∧ ∃ i, b.repr u i = 1 := by sorry
