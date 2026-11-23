-- Prove2me | Theorems.Thm_GlobalTheory_MulUnramified_le_preimage_of_comp
-- name    : GlobalTheory.MulUnramified.le_preimage_of_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:35.77953+00:00
-- url     : https://prove2.me/theorems/2769446d-9405-4ee6-877f-d4af03de66b7
-- title:
--   Mul Unramified: le preimage of comp
-- statement:
--   The Mul Unramified construction uses the le preimage of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L45-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulUnramified

theorem GlobalTheory.MulUnramified.le_preimage_of_comp {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X)
    {V : X.Opens} {V' : P.Opens} {W : T.Opens} (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V') :
    W ≤ (a ≫ p) ⁻¹ᵁ V := by sorry
