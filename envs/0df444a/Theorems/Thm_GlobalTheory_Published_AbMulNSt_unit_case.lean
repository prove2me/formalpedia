-- Prove2me | Theorems.Thm_GlobalTheory_Published_AbMulNSt_unit_case
-- name    : GlobalTheory.Published.AbMulNSt.unit_case
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:17.284327+00:00
-- url     : https://prove2.me/theorems/3cb1679e-513e-44ab-a03b-f9bda7dbff10
-- title:
--   Ab Mul NSt: unit case
-- statement:
--   The Ab Mul NSt construction uses the unit case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/DimEqZero.lean#L36-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/DimEqZero.lean#L36-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3
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
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.AbMulNSt
variable {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] {g n : ℕ}
omit [IsAlgClosed k]

theorem GlobalTheory.Published.AbMulNSt.unit_case (n : ℕ) : IsAbelianScheme (𝟙_ (Over (Sp k))) ∧
    SmoothOfRelativeDimension 0 (𝟙_ (Over (Sp k))).hom ∧
    Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ 𝟙_ (Over (Sp k))) // x ^ n = 1} = n ^ (2 * 0) := by sorry
