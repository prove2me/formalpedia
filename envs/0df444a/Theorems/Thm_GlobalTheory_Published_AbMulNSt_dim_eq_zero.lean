-- Prove2me | Theorems.Thm_GlobalTheory_Published_AbMulNSt_dim_eq_zero
-- name    : GlobalTheory.Published.AbMulNSt.dim_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:08.99302+00:00
-- url     : https://prove2.me/theorems/b6ba9dab-57d9-504d-8a40-afb277411e8d
-- title:
--   Ab Mul NSt: dim eq zero
-- statement:
--   The Ab Mul NSt construction uses the dim eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/DimEqZero.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/DimEqZero.lean#L25-L32

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

theorem GlobalTheory.Published.AbMulNSt.dim_eq_zero (h : AbMulNSt) (hB : IsAbelianScheme B) (hg : SmoothOfRelativeDimension g B.hom)
    (hn : (n : k) ≠ 0) (h2 : 2 ≤ n) (ht : ∀ x : 𝟙_ (Over (Sp k)) ⟶ B, x ^ n = 1 → x = 1) :
    g = 0 := by sorry
