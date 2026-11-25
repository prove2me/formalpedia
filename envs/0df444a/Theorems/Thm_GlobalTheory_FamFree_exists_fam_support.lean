-- Prove2me | Theorems.Thm_GlobalTheory_FamFree_exists_fam_support
-- name    : GlobalTheory.FamFree.exists_fam_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:36.887995+00:00
-- url     : https://prove2.me/theorems/eac934ab-8dcf-41c9-a248-330d28ad5af1
-- title:
--   Fam Free: exists fam support
-- statement:
--   The Fam Free construction uses the exists fam support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFamOfReps.lean#L145-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFamOfReps.lean#L145-L151

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

theorem GlobalTheory.FamFree.exists_fam_support (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ s : Fam D F k, ∀ β : D.X, (¬ ∀ j, (s.s β).f j = 0) ↔ ∃ mu, α + k • mu = β := by sorry
