-- Prove2me | Theorems.Thm_GlobalTheory_SS_unr_self
-- name    : GlobalTheory.SS.unr_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:37.3168+00:00
-- url     : https://prove2.me/theorems/8b0d78bd-2e60-48bc-8ccf-a4d0bfa9cd4e
-- title:
--   SS: unr self
-- statement:
--   The SS construction uses the unr self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfDerivationFnOn.lean#L337-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfDerivationFnOn.lean#L337-L338

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
variable {R} {A A' : Over (Sp K)}

theorem GlobalTheory.SS.unr_self {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R} (h : Irreducible π) :
    Unr π R := by sorry
