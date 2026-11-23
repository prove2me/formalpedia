-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_mem_rationalPart
-- name    : GlobalTheory.GaloisDescent.mem_rationalPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:16.317076+00:00
-- url     : https://prove2.me/theorems/c2b87800-a625-48ba-9841-7ccc44660b1e
-- title:
--   Galois Descent: mem rational Part
-- statement:
--   The Galois Descent construction uses the mem rational Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L254-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L254-L255

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

theorem GlobalTheory.GaloisDescent.mem_rationalPart {W : Submodule L (L ⊗[K] V)} {v : V} :
    v ∈ rationalPart K W ↔ (1 : L) ⊗ₜ[K] v ∈ W := by sorry
