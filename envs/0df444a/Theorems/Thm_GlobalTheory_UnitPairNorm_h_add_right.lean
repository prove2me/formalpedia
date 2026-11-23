-- Prove2me | Theorems.Thm_GlobalTheory_UnitPairNorm_h_add_right
-- name    : GlobalTheory.UnitPairNorm.h_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:42.789496+00:00
-- url     : https://prove2.me/theorems/96a5c009-81d7-4d27-aaa1-f68f0f5fc828
-- title:
--   Unit Pair Norm: h add right
-- statement:
--   The Unit Pair Norm construction uses the h add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L16-L20

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]

theorem GlobalTheory.UnitPairNorm.h_add_right (c : E ≃+* E) (h : V → V → E)
    (hadd : ∀ x y z : V, h (x + y) z = h x z + h y z)
    (hsym : ∀ x y : V, h y x = c (h x y)) (y a b : V) :
    h y (a + b) = h y a + h y b := by sorry
