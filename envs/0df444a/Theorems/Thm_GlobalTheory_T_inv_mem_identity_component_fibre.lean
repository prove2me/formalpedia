-- Prove2me | Theorems.Thm_GlobalTheory_T_inv_mem_identity_component_fibre
-- name    : GlobalTheory.T.inv_mem_identity_component_fibre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:30.532569+00:00
-- url     : https://prove2.me/theorems/63dae3f5-6f39-4310-94c9-afa38ccd66e6
-- title:
--   T: inv mem identity component fibre
-- statement:
--   The T construction uses the inv mem identity component fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvMemConnectedComponentInFibreStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvMemConnectedComponentInFibreStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvMemConnectedComponentInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvMemConnectedComponentInFibreStatement
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

theorem GlobalTheory.T.inv_mem_identity_component_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left), y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by sorry
