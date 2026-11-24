-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_baseChange_rationalPart
-- name    : GlobalTheory.GaloisDescent.baseChange_rationalPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:39.178636+00:00
-- url     : https://prove2.me/theorems/a5cad2de-add2-4d36-8cda-c16823fd5966
-- title:
--   Galois Descent: base Change rational Part
-- statement:
--   The Galois Descent construction uses the base Change rational Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L266-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L266-L273

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
variable {K L V G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]

theorem GlobalTheory.GaloisDescent.baseChange_rationalPart (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (W : Submodule L (L ⊗[K] V)) (hW : ∀ g, ∀ w ∈ W, (s g).toLinearMap.rTensor V w ∈ W) :
    (rationalPart K W).baseChange L = W := by sorry
