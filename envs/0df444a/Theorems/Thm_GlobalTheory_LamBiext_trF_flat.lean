-- Prove2me | Theorems.Thm_GlobalTheory_LamBiext_trF_flat
-- name    : GlobalTheory.LamBiext.trF_flat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:09.892742+00:00
-- url     : https://prove2.me/theorems/2e81dd34-1294-4197-a6bd-870faa73e3f1
-- title:
--   Lam Biext: tr F flat
-- statement:
--   The Lam Biext construction uses the tr F flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L33-L41

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

theorem GlobalTheory.LamBiext.trF_flat (r : Z ⟶ Y) (z : Z) (j j' : K → I → L.ι) :
    trF (L := L) (flatφ φ ψ) (flatε δ ε) r z (fun p => j p.1 p.2) (fun p => j' p.1 p.2) =
      ∏ k, trF (L := L) φ δ (r ≫ ψ k) z (j k) (j' k) ^ ε k := by sorry
