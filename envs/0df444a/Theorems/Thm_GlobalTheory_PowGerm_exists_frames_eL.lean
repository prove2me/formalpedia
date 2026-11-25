-- Prove2me | Theorems.Thm_GlobalTheory_PowGerm_exists_frames_eL
-- name    : GlobalTheory.PowGerm.exists_frames_eL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:48:25.242144+00:00
-- url     : https://prove2.me/theorems/091e434a-ac78-4170-8d40-567fdf5afade
-- title:
--   Pow Germ: exists frames e L
-- statement:
--   The Pow Germ construction uses the exists frames e L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsFramesEL.lean#L19-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsFramesEL.lean#L19-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsFramesEL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.PowGerm

theorem GlobalTheory.PowGerm.exists_frames_eL {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
    (t : SAB H (Sp V)) (L' : LB t.G.left) (h : t.PP.L = L')
    (d : ℕ) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d)
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t)
    (hch : IsChartG t (𝟙 (Sp V)) d FT act tg uv x) (hfr : IsFrameG t (𝟙 (Sp V)) d x FT act ph1 ph2 sy ad e)
    (hpr : IsPrimG t wP) :
    ∃ τ : Frames L' (κ := Fin 1 × Fin d) x, τ.Gen ∧
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → L'.ι), Good L' y J →
        val (τ m) (𝟙 _) y J = val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP m)) (𝟙 _) y J) ∧
      (FrTrunc t (𝟙 (Sp V)) d x e → τ.Trunc) := by sorry
