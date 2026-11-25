-- Prove2me | Theorems.Thm_GlobalTheory_UnitRigidity_mem_range_of_forall_valuationSubring
-- name    : GlobalTheory.UnitRigidity.mem_range_of_forall_valuationSubring
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:13.58064+00:00
-- url     : https://prove2.me/theorems/d31b7c67-b0e0-4733-8fbb-e814ebd4f34b
-- title:
--   Unit Rigidity: mem range of forall valuation Subring
-- statement:
--   The Unit Rigidity construction uses the mem range of forall valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L120-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L120-L138

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.UnitRigidity

theorem GlobalTheory.UnitRigidity.mem_range_of_forall_valuationSubring {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    (x : L) (h : ∀ O : ValuationSubring L, (∀ k, algebraMap K L k ∈ O) → x ∈ O) :
    x ∈ Set.range (algebraMap K L) := by sorry
