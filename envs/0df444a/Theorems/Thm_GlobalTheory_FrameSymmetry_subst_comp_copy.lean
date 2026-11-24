-- Prove2me | Theorems.Thm_GlobalTheory_FrameSymmetry_subst_comp_copy
-- name    : GlobalTheory.FrameSymmetry.subst_comp_copy
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:20.549829+00:00
-- url     : https://prove2.me/theorems/715d7c6a-c5e0-4f54-8dd4-e7f8ee9b5f29
-- title:
--   Frame Symmetry: subst comp copy
-- statement:
--   The Frame Symmetry construction uses the subst comp copy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsSymmetrySeriesOfFrames.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsSymmetrySeriesOfFrames.lean#L27-L33

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSymmetrySeriesOfFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.FrameSymmetry
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
variable {S : Type} [CommRing S] (d : ℕ)

theorem GlobalTheory.FrameSymmetry.subst_comp_copy (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)).comp (jetCopy d m i) =
      jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2) := by sorry
