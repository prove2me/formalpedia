-- Prove2me | Theorems.Thm_GlobalTheory_torsion_points_integral
-- name    : GlobalTheory.torsion_points_integral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:29:49.284951+00:00
-- url     : https://prove2.me/theorems/8d1310f1-f2a5-54cf-a6a1-f9232af7c375
-- title:
--   Global Theory: torsion points integral
-- statement:
--   The Global Theory construction uses the torsion points integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L386-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L386-L455

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open TorsionIntegral

theorem GlobalTheory.torsion_points_integral :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (N : ℕ), 1 ≤ N →
      ∀ s : Finset (GtPtF D (Kbar V)), (∀ g ∈ s, GtTors D N g) →
      ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (Kbar V) ⟶ TA V W),
        FinExt V W ∧ ∀ g ∈ s, ∃ g' : GtPt D (TA V W), GtPt.IsPullF (Kbar V) φ.left g' g ∧
          ∃ h, GtPt.IsNsmul N g' h ∧ h.IsZero := by sorry
