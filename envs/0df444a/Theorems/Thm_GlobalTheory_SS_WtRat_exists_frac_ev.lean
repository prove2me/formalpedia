-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_exists_frac_ev
-- name    : GlobalTheory.SS.WtRat.exists_frac_ev
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:36:57.615795+00:00
-- url     : https://prove2.me/theorems/7d244ef3-5d40-4c2a-a152-e75cde864c6c
-- title:
--   Wt Rat: exists frac ev
-- statement:
--   The Wt Rat construction uses the exists frac ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFractionEvalSectionAffineNearPoint.lean#L19-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFractionEvalSectionAffineNearPoint.lean#L19-L53

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

theorem GlobalTheory.SS.WtRat.exists_frac_ev (R : Type) [CommRing R] (W : (Sp R).Opens) (s : Γ(Sp R, W))
    (x : PrimeSpectrum R) (hx : x ∈ W) :
    ∃ α β : R, β ∉ x.asIdeal ∧ ∀ (F : Type) [Field F] (e : R →+* F) (h : ⊤ ≤ spMap e ⁻¹ᵁ W),
      WtRat.ev (spMap e) W h s * e β = e α := by sorry
