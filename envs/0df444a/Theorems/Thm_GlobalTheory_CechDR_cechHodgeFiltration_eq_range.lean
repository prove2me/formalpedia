-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_cechHodgeFiltration_eq_range
-- name    : GlobalTheory.CechDR.cechHodgeFiltration_eq_range
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:20.622011+00:00
-- url     : https://prove2.me/theorems/d2e03135-2e3b-4d3d-aab8-7678d55db401
-- title:
--   Cech DR: cech Hodge Filtration eq range
-- statement:
--   The Cech DR construction uses the cech Hodge Filtration eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ComparisonMemCechHodgeFiltration.lean#L216-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ComparisonMemCechHodgeFiltration.lean#L216-L216

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
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
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh Cris
universe v u v' u'
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem GlobalTheory.CechDR.cechHodgeFiltration_eq_range (s : X ⟶ Sp R) : CechHodgeFiltration s = LinearMap.range (clForm s) := by sorry
