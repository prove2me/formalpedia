-- Prove2me | Theorems.Thm_GlobalTheory_UT_PhiOrder_exists_kap
-- name    : GlobalTheory.UT.PhiOrder.exists_kap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:20:10.951279+00:00
-- url     : https://prove2.me/theorems/591825e6-2c82-4c62-ac87-4de2114970e2
-- title:
--   Phi Order: exists kap
-- statement:
--   The Phi Order construction uses the exists kap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L239-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L239-L261

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.PhiOrder
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D}

theorem GlobalTheory.UT.PhiOrder.exists_kap (m k : ℕ) (hk : k = 2 * m + 1) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ k) (k ^ 2) 1), Normd κ ∧
      ∀ T (x : T ⟶ D.P.A) z J, Good D.P.L z J → val κ x.left z J =
        (th D z J (x ^ k) (x ^ k)⁻¹ (x ^ k) * (val D.sym (x ^ k).left z J)⁻¹ * pot (th D z J) x (2 * k)) ^ m *
          (pot (th D z J) x k ^ (k + 2 * m))⁻¹ := by sorry
