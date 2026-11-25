-- Prove2me | Theorems.Thm_GlobalTheory_ExpUniq_sval_sec_eq_zero
-- name    : GlobalTheory.ExpUniq.sval_sec_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:05:40.655808+00:00
-- url     : https://prove2.me/theorems/f072191b-7794-47f8-981a-5da283ea4cf8
-- title:
--   Exp Uniq: sval sec eq zero
-- statement:
--   The Exp Uniq construction uses the sval sec eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalEqZeroOfWeightSum.lean#L225-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalEqZeroOfWeightSum.lean#L225-L242

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ExpUniq
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {U : PreU I D A G} {T : Over (Spec (CommRingCat.of R))} {k : ℕ} {σ σ' : U.SecGT T k} {f f' : ∀ α, SecBT D T k α}

theorem GlobalTheory.ExpUniq.sval_sec_eq_zero (h : U.ExpT T k σ f)
    (hf : ∀ α (Z : Scheme.{0}) (r : Z ⟶ _) z J, Good D.P.L z J → sval (f α) r z J = 0) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ G).left) (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (ha : (r ≫ (snd T G).left) ≫ G.hom = a ≫ thick R I e) (z : Z) (JG) (hJG : Good U.P.L.L z JG) :
    sval σ r z JG = 0 := by sorry
