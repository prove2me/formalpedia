-- Prove2me | Theorems.Thm_GlobalTheory_mem_matroid_closure_of_mem_adjoin
-- name    : GlobalTheory.mem_matroid_closure_of_mem_adjoin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:55:21.859+00:00
-- url     : https://prove2.me/theorems/003966ea-ae40-4b9f-af64-9e5f719f6f57
-- title:
--   Global Theory: mem matroid closure of mem adjoin
-- statement:
--   The Global Theory construction uses the mem matroid closure of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsAlgebraicIndependentRatiosOfGenericZero.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsAlgebraicIndependentRatiosOfGenericZero.lean#L8-L12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsAlgebraicIndependentRatiosOfGenericZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open GlobalTheory

theorem GlobalTheory.mem_matroid_closure_of_mem_adjoin {k κ : Type} [Field k] [Field κ] [Algebra k κ]
    {S : Set κ} {x : κ} (hx : x ∈ Algebra.adjoin k S) :
    x ∈ (AlgebraicIndependent.matroid k κ).closure S := by sorry
