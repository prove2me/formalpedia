-- Prove2me | Theorems.Thm_GlobalTheory_FrameGeo_series_ext_one
-- name    : GlobalTheory.FrameGeo.series_ext_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:05.388385+00:00
-- url     : https://prove2.me/theorems/ce2a8c6f-0da7-4f7b-b10d-f731d40af0f5
-- title:
--   Frame Geo: series ext one
-- statement:
--   The Frame Geo construction uses the series ext one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ThreePointSeriesExponentialOfDefect.lean#L241-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ThreePointSeriesExponentialOfDefect.lean#L241-L291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer.FBOf
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.FrameGeo.series_ext_one (hJet : JetAlgSt) (hRep : RepSt) (Lr : RigLB G) (c : CubicalStr G Lr) {O : Type} [CommRing O]
    [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε))
    {d : ℕ} (x : Fam G (Fin d)) (hx : IsUnivChart G d x) (j : Lr.L.ι) (B : FB R d O) (hB : IsFBOf Lr c act u x j B)
    (g g' : PS R 1 d)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J : (T.left ⟶ G.left) → Lr.L.ι), Good Lr.L z J →
      ∀ (Φ : PS R 1 d →+* T.left.presheaf.stalk z) (y : T ⟶ G),
      (∀ r : R, Φ (C r) = gs T.hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) →
      (∀ (K : Type) [Fintype K] (φ : K → (G.left ⟶ G.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb Lr.L φ ε))
        (s : PS R 1 d), IsSer1 x _ (t.s (fun _ => j)).val s → ∀ a,
          Φ (ev ![B.A.act a] s) = (val t (y ≫ act.act a).left z J).val) →
      (∀ a b e, Φ (ev ![B.A.act a, B.A.act b, B.A.act e] B.ph2) =
        (cubV c z J (y ≫ act.act a) (y ≫ act.act b) (y ≫ act.act e)).val) →
      (∀ o a b, Φ (ev ![B.A.act a, B.A.act b] (B.ad o)) =
        (val₂ (u o) z J (y ≫ act.act a) (y ≫ act.act b))⁻¹.val) → Φ g = Φ g') :
    g = g' := by sorry
