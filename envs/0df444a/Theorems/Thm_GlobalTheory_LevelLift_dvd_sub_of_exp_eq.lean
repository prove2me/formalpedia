-- Prove2me | Theorems.Thm_GlobalTheory_LevelLift_dvd_sub_of_exp_eq
-- name    : GlobalTheory.LevelLift.dvd_sub_of_exp_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:37.189638+00:00
-- url     : https://prove2.me/theorems/ee40acfd-5580-4b38-a7c1-d7d178c6ac65
-- title:
--   Level Lift: dvd sub of exp eq
-- statement:
--   The Level Lift construction uses the dvd sub of exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticeLiftOfLevelSection.lean#L46-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticeLiftOfLevelSection.lean#L46-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticeLiftOfLevelSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open GlobalTheory GlobalTheory.LevelLift

theorem GlobalTheory.LevelLift.dvd_sub_of_exp_eq (k : ℕ) (hk : 0 < k) (m n : ℤ)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : (k : ℤ) ∣ n - m := by sorry
