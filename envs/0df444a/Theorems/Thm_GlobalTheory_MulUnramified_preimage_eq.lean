-- Prove2me | Theorems.Thm_GlobalTheory_MulUnramified_preimage_eq
-- name    : GlobalTheory.MulUnramified.preimage_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:01.428808+00:00
-- url     : https://prove2.me/theorems/1e3eeab1-cd6c-4303-a003-f51110879fc8
-- title:
--   Mul Unramified: preimage eq
-- statement:
--   The Mul Unramified construction uses the preimage eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L24-L29

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

theorem GlobalTheory.MulUnramified.preimage_eq {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) (hi : Function.Surjective i) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) : f ⁻¹ᵁ V = g ⁻¹ᵁ V := by sorry
