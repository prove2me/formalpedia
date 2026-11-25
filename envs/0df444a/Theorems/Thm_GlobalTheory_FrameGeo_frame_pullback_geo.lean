-- Prove2me | Theorems.Thm_GlobalTheory_FrameGeo_frame_pullback_geo
-- name    : GlobalTheory.FrameGeo.frame_pullback_geo
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:39.242641+00:00
-- url     : https://prove2.me/theorems/80178dae-f89c-460c-940e-a5778ba02d0b
-- title:
--   Frame Geo: frame pullback geo
-- statement:
--   The Frame Geo construction uses the frame pullback geo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ThreePointSeriesExponentialOfDefect.lean#L297-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ThreePointSeriesExponentialOfDefect.lean#L297-L346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (isCub_cubV cubV val₂)

theorem GlobalTheory.FrameGeo.frame_pullback_geo : JetAlgSt → RepSt → SerSt → SerExSt → RosIdSt → ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Function.Surjective G.hom.appTop.hom → Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, IsNormRos Lr.L _ _ (u a)) → ∀ (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x → ∀ j : Lr.L.ι, ⊤ ≤ η[G].left ⁻¹ᵁ Lr.L.U j → ∀ B : FB R d O, IsFBOf Lr c act u x j B → ∀ (w0 : O) (ρ : LB.Gen (LB.LinComb Lr.L (primφ (act.act w0)) primε)), ρ.IsGen → ∀ (a : O) (N : ℕ), a * star a = (N : O) → (∃ mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, (act.act a).left] ![(N : ℤ), -1]), mu.IsGen) ∧ ∀ mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, (act.act a).left] ![(N : ℤ), -1]), mu.IsGen → ∀ M r : PS R 1 d, IsSer1 x _ (mu.s (fun _ => j)).val M → IsSer1 x _ (ρ.s (fun _ => j)).val r → ∃ (w : PS R 1 d) (κ : Rˣ), w * r ^ N = C (κ : R) * M * ev (n := 1) ![B.A.act a] r ∧ ∀ (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d), B.IsCanonGauge k h → FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) := by sorry
