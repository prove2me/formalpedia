-- Prove2me | Theorems.Thm_GlobalTheory_DimCodim_dim_add_le_of_le_coheight
-- name    : GlobalTheory.DimCodim.dim_add_le_of_le_coheight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:24.854838+00:00
-- url     : https://prove2.me/theorems/2c76a05a-a8d4-4c29-9666-a3010cd6deaf
-- title:
--   Dim Codim: dim add le of le coheight
-- statement:
--   The Dim Codim construction uses the dim add le of le coheight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosedComplementDimBound.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosedComplementDimBound.lean#L13-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedComplementDimBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.DimCodim
attribute [local instance low] specializationOrder

theorem GlobalTheory.DimCodim.dim_add_le_of_le_coheight {S W : Type*} [TopologicalSpace S] [TopologicalSpace W]
    [QuasiSober S] [T0Space S] [QuasiSober W] [T0Space W] {j : W → S} (hj : Continuous j)
    (hi : Function.Injective j) (c : ℕ∞) (h : ∀ w, c ≤ Order.coheight (j w)) :
    topologicalKrullDim W + c ≤ topologicalKrullDim S := by sorry
