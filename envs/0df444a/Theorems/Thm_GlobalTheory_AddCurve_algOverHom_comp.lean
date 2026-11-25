-- Prove2me | Theorems.Thm_GlobalTheory_AddCurve_algOverHom_comp
-- name    : GlobalTheory.AddCurve.algOverHom_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:34.556399+00:00
-- url     : https://prove2.me/theorems/8a0ce3c2-eb30-50b8-ae57-45a87d084ef8
-- title:
--   Add Curve: alg Over Hom comp
-- statement:
--   The Add Curve construction uses the alg Over Hom comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TopLeAlgOverHom.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TopLeAlgOverHom.lean#L43-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TopLeAlgOverHom
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AddCurve
variable {k : Type} [CommRing k]

theorem GlobalTheory.AddCurve.algOverHom_comp {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (f : A →ₐ[k] B) (h : B →ₐ[k] C) : algOverHom h ≫ algOverHom f = algOverHom (h.comp f) := by sorry
