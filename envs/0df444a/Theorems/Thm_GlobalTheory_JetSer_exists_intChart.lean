-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_exists_intChart
-- name    : GlobalTheory.JetSer.exists_intChart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:29.557014+00:00
-- url     : https://prove2.me/theorems/3983ce88-3326-4b02-ba6d-338aad577cf7
-- title:
--   Jet Ser: exists int Chart
-- statement:
--   The Jet Ser construction uses the exists int Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsIndexOfLocal.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsIndexOfLocal.lean#L17-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIndexOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer

theorem GlobalTheory.JetSer.exists_intChart : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (f g : G ⟶ G) [IsMonHom f] [IsMonHom g], LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) → (∃ u, IsNormRos L f g u) ∧ (Function.Surjective (G ⊗ G).hom.appTop.hom → ∀ u u', IsNormRos L f g u → IsNormRos L f g u' → u.s = u'.s)) → FBOfSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom], Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G), (∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] Lr.L) (cubeLB G ![fst G G, snd G G ≫ act.act (star a)] Lr.L)) → ∃ (d : ℕ) (x : Fam G (Fin d)) (j : Lr.L.ι) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)) (B : FB R d O), IsUnivChart G d x ∧ ⊤ ≤ η[G].left ⁻¹ᵁ Lr.L.U j ∧ (∀ a, IsNormRos Lr.L _ _ (u a)) ∧ IsFBOf Lr c act u x j B := by sorry
