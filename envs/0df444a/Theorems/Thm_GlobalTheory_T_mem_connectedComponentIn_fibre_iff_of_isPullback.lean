-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_connectedComponentIn_fibre_iff_of_isPullback
-- name    : GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:02.920004+00:00
-- url     : https://prove2.me/theorems/9a864754-3938-4eaa-b252-28ba432bc52d
-- title:
--   T: mem connected Component In fibre iff of is Pullback
-- statement:
--   The T construction uses the mem connected Component In fibre iff of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComponentInFibreIffOfIsPullbackStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComponentInFibreIffOfIsPullbackStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullbackStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s)) (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s → ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by sorry
