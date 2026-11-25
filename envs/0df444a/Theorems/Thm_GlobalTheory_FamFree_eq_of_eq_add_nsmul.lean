-- Prove2me | Theorems.Thm_GlobalTheory_FamFree_eq_of_eq_add_nsmul
-- name    : GlobalTheory.FamFree.eq_of_eq_add_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:31.317192+00:00
-- url     : https://prove2.me/theorems/577c74d8-ae31-4913-955c-98af64aa42b5
-- title:
--   Fam Free: eq of eq add nsmul
-- statement:
--   The Fam Free construction uses the eq of eq add nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFamOfReps.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFamOfReps.lean#L42-L48

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

theorem GlobalTheory.FamFree.eq_of_eq_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s t : Fam D F k) {α β : D.X} (hβ : ∃ mu, α + k • mu = β)
    (h : s.s α = t.s α) : s.s β = t.s β := by sorry
