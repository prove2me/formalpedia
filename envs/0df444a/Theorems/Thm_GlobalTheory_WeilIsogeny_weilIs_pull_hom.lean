-- Prove2me | Theorems.Thm_GlobalTheory_WeilIsogeny_weilIs_pull_hom
-- name    : GlobalTheory.WeilIsogeny.weilIs_pull_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:33.697845+00:00
-- url     : https://prove2.me/theorems/84202a9d-0836-4e8e-aa38-743fa5dede7f
-- title:
--   Weil Isogeny: weil Is pull hom
-- statement:
--   The Weil Isogeny construction uses the weil Is pull hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenMovePow.lean#L130-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenMovePow.lean#L130-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenMovePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilIsogeny
open CommutatorPairing
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem GlobalTheory.WeilIsogeny.weilIs_pull_hom (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (ψ : A ⟶ B)
    [IsMonHom ψ] {d : ℕ} (hw : LBIso (lbPow L d) (M.pull ψ.left)) {n : ℤ} {T : Over S} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs B M n (x ≫ ψ) (y ≫ ψ) c) : WeilIs A L (n * d) x y c := by sorry
