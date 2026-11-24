-- Prove2me | Theorems.Thm_GlobalTheory_inv_mem_connectedComponentIn_fibre
-- name    : GlobalTheory.inv_mem_connectedComponentIn_fibre
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:55.497496+00:00
-- url     : https://prove2.me/theorems/1e6858e7-052f-4c5e-b650-ed5192af24cb
-- title:
--   Global Theory: inv mem connected Component In fibre
-- statement:
--   The Global Theory construction uses the inv mem connected Component In fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvMemConnectedComponentInFibre.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvMemConnectedComponentInFibre.lean#L8-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvMemConnectedComponentInFibre
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
open GlobalTheory

theorem GlobalTheory.inv_mem_connectedComponentIn_fibre (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left)
    (hy : y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) :
    (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by sorry
