-- Prove2me | Theorems.Thm_GlobalTheory_FamFree_exists_fam_single
-- name    : GlobalTheory.FamFree.exists_fam_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:57.222511+00:00
-- url     : https://prove2.me/theorems/a6a10e77-3db1-4c8e-acec-c984118cd752
-- title:
--   Fam Free: exists fam single
-- statement:
--   The Fam Free construction uses the exists fam single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFamOfReps.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFamOfReps.lean#L55-L58

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

theorem GlobalTheory.FamFree.exists_fam_single (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (ρ : D.X)
    (σ : FamSec D F k ρ) :
    ∃ s : Fam D F k, s.s ρ = σ ∧ ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (s.s β).f j = 0 := by sorry
