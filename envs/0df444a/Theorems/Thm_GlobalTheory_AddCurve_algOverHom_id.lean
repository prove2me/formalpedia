-- Prove2me | Theorems.Thm_GlobalTheory_AddCurve_algOverHom_id
-- name    : GlobalTheory.AddCurve.algOverHom_id
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:29.496092+00:00
-- url     : https://prove2.me/theorems/145d7536-d363-4c0a-8bcb-e3e9e59a63bf
-- title:
--   Add Curve: alg Over Hom id
-- statement:
--   The Add Curve construction uses the alg Over Hom id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TopLeAlgOverHom.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TopLeAlgOverHom.lean#L49-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TopLeAlgOverHom
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

theorem GlobalTheory.AddCurve.algOverHom_id (A : Type) [CommRing A] [Algebra k A] : algOverHom (AlgHom.id k A) = 𝟙 _ := by sorry
