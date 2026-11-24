-- Prove2me | Theorems.Thm_GlobalTheory_FramePartialLaw_pt_law
-- name    : GlobalTheory.FramePartialLaw.pt_law
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:38:19.273663+00:00
-- url     : https://prove2.me/theorems/764906f0-8593-47dd-ad76-310dca210afc
-- title:
--   Frame Partial Law: pt law
-- statement:
--   The Frame Partial Law construction uses the pt law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFirstPartialLawSeriesOfFrames.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFirstPartialLawSeriesOfFrames.lean#L54-L59

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSymmetrySeriesOfFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFirstPartialLawSeriesOfFrames
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.FramePartialLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameSymmetry
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem GlobalTheory.FramePartialLaw.pt_law (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (r : Fin 2 → Fin n) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (F p.2))) ≫ x m =
      jptG t x0 d x m (r 0) * jptG t x0 d x m (r 1) := by sorry
