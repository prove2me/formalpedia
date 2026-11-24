-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_FBOf_series_ext
-- name    : GlobalTheory.JetSer.FBOf.series_ext
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:40:47.169777+00:00
-- url     : https://prove2.me/theorems/75fe83f1-7e9a-4020-8bfd-f2f5ff6278cc
-- title:
--   FBOf: series ext
-- statement:
--   The FBOf construction uses the series ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGoodConst.lean#L48-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGoodConst.lean#L48-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_val val val_of Good cubV val₂ IsCub isCub_cubV exists_chart psum_hom preHom)
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FBOf
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.JetSer.FBOf.series_ext (hJet : JetAlgSt) (hRep : RepSt) (Lr : RigLB G) (c : CubicalStr G Lr) {O : Type} [CommRing O]
    [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε))
    {d : ℕ} (x : Fam G (Fin d)) (hx : IsUnivChart G d x) (j : Lr.L.ι)
    (F : Fin d → PS R 2 d) (hF : IsLawOf x F) (α : O → Pt R 1 d) (hα : ∀ a, IsMapOf x x (act.act a) (α a))
    (ph : PS R 3 d) (hph : IsSer3 x _ (c.t.s (fun _ => j)).val ph)
    (ad : O → PS R 2 d) (had : ∀ a, IsSer2 x _ ((u a).s (fun _ => j))⁻¹.val (ad a))
    (n : ℕ) (g g' : PS R n d)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J : (T.left ⟶ G.left) → Lr.L.ι), Good Lr.L z J →
      ∀ (Φ : PS R n d →+* T.left.presheaf.stalk z) (y : Pt R n d → (T ⟶ G)), y 0 = 1 →
      (∀ a b, GP a → GP b → y (addOf F a b) = y a * y b) →
      (∀ o a, GP a → y (comp1 (α o) a) = y a ≫ act.act o) →
      (∀ a b e, GP a → GP b → GP e → Φ (ev ![a, b, e] ph) = (cubV c z J (y a) (y b) (y e)).val) →
      (∀ o a b, GP a → GP b → Φ (ev ![a, b] (ad o)) = (val₂ (u o) z J (y a) (y b))⁻¹.val) → Φ g = Φ g') :
    g = g' := by sorry
