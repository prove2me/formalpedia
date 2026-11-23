-- Prove2me | Theorems.Thm_GlobalTheory_FamFree_zero_of_eq_add_nsmul
-- name    : GlobalTheory.FamFree.zero_of_eq_add_nsmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:42.901543+00:00
-- url     : https://prove2.me/theorems/fd9ab832-0f19-4698-8d60-2afe3ffc6583
-- title:
--   Fam Free: zero of eq add nsmul
-- statement:
--   The Fam Free construction uses the zero of eq add nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFamOfReps.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFamOfReps.lean#L33-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamFree
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.FamFree.zero_of_eq_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) {α β : D.X} (hβ : ∃ mu, α + k • mu = β)
    (h : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s β).f j = 0 := by sorry
