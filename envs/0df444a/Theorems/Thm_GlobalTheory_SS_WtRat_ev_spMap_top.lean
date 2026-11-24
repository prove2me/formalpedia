-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_ev_spMap_top
-- name    : GlobalTheory.SS.WtRat.ev_spMap_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:37:12.241068+00:00
-- url     : https://prove2.me/theorems/c0fb6fb2-eb5b-441e-a627-9cd8e60ec69a
-- title:
--   Wt Rat: ev sp Map top
-- statement:
--   The Wt Rat construction uses the ev sp Map top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFractionEvalSectionAffineNearPoint.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFractionEvalSectionAffineNearPoint.lean#L12-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFractionEvalSectionAffineNearPoint
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
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat

theorem GlobalTheory.SS.WtRat.ev_spMap_top {R F : Type} [CommRing R] [CommRing F] (e : R →+* F)
    (h : ⊤ ≤ spMap e ⁻¹ᵁ ⊤) (u : Γ(Sp R, ⊤)) :
    ev (spMap e) ⊤ h u = e ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u) := by sorry
