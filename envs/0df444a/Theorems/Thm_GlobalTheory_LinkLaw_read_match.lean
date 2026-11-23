-- Prove2me | Theorems.Thm_GlobalTheory_LinkLaw_read_match
-- name    : GlobalTheory.LinkLaw.read_match
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:55.145805+00:00
-- url     : https://prove2.me/theorems/815c3d2d-8506-41b7-a43d-04bca3c9a78c
-- title:
--   Link Law: read match
-- statement:
--   The Link Law construction uses the read match property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsLawOfOfMatch.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsLawOfOfMatch.lean#L40-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LinkLaw
variable {V : Type} [CommRing V]

theorem GlobalTheory.LinkLaw.read_match {G : Over (Sp V)} {κ : Type} {N m : ℕ} (z : overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G)
    (x : Chart.sp (R₀ := V) (Chart.JetR V (Fin N) m) ⟶ G) (e : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m)
    (he : z.left = Geo.Tor.spMap (e : Chart.JetR V (Fin N) m →+* Jet V κ m) ≫ x.left)
    {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (S : Jet V κ m →ₐ[V] B) (Φ : B →ₐ[V] A) :
    (toAt A ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) Φ) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) S ≫ z =
      Chart.spMap (Φ.comp (S.comp (e : Chart.JetR V (Fin N) m →ₐ[V] Jet V κ m))) ≫ x := by sorry
