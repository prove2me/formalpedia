-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_stable_iff_exists_baseChange
-- name    : GlobalTheory.GaloisDescent.stable_iff_exists_baseChange
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:48:40.784801+00:00
-- url     : https://prove2.me/theorems/e28caacc-d728-4175-8a88-a2d5f529fb3a
-- title:
--   Galois Descent: stable iff exists base Change
-- statement:
--   The Galois Descent construction uses the stable iff exists base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L275-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L275-L284

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

theorem GlobalTheory.GaloisDescent.stable_iff_exists_baseChange (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (W : Submodule L (L ⊗[K] V)) :
    (∀ g, ∀ w ∈ W, (s g).toLinearMap.rTensor V w ∈ W) ↔
      ∃! N : Submodule K V, N.baseChange L = W := by sorry
