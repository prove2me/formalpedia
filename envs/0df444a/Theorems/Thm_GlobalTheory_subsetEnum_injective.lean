-- Prove2me | Theorems.Thm_GlobalTheory_subsetEnum_injective
-- name    : GlobalTheory.subsetEnum_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:07.233611+00:00
-- url     : https://prove2.me/theorems/096ee402-3d5e-4b71-b343-f55c55b9a86f
-- title:
--   Global Theory: subset Enum injective
-- statement:
--   The Global Theory construction uses the subset Enum injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {R : Type*} [CommRing R]

theorem GlobalTheory.subsetEnum_injective {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Function.Injective (subsetEnum S) := by sorry
