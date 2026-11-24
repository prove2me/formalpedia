-- Prove2me | Theorems.Thm_GlobalTheory_LamBiext_val_nest
-- name    : GlobalTheory.LamBiext.val_nest
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:58:11.100868+00:00
-- url     : https://prove2.me/theorems/1c217c03-c1a9-424f-a26d-9f8e55166518
-- title:
--   Lam Biext: val nest
-- statement:
--   The Lam Biext construction uses the val nest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L62-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L62-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X W Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]
  (φ : I → (W ⟶ X)) (δ : I → ℤ) (ψ : K → (Y ⟶ W)) (ε : K → ℤ)
variable {L φ δ ψ ε}

theorem GlobalTheory.LamBiext.val_nest {t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z}
    {JP : (Z ⟶ W) → I → L.ι} (hJP : Good (LB.LinComb L φ δ) z JP) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (L := LB.LinComb L φ δ) (nest L φ δ ψ ε t) r z JP =
      (∏ k, adj φ δ z JP J (r ≫ ψ k) ^ ε k) * val (L := L) t r z J := by sorry
