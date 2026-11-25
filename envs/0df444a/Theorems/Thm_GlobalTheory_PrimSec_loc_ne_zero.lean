-- Prove2me | Theorems.Thm_GlobalTheory_PrimSec_loc_ne_zero
-- name    : GlobalTheory.PrimSec.loc_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:01:23.623752+00:00
-- url     : https://prove2.me/theorems/1da927a1-1762-4823-83af-5ecf50aa67ab
-- title:
--   Prim Sec: loc ne zero
-- statement:
--   The Prim Sec construction uses the loc ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L245-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L245-L256

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {X XK : Scheme.{0}} {j : XK ⟶ X} {M : LB X}

theorem GlobalTheory.PrimSec.loc_ne_zero [IsIntegral XK] (σ : LB.Sec (M.pull j)) (hσ : ∃ i, σ.f i ≠ 0) (i : M.ι) {V : X.Opens}
    (hV : V ≤ M.U i) (hne : Nonempty (j ⁻¹ᵁ V)) : loc σ i hV ≠ 0 := by sorry
