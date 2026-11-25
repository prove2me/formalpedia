-- Prove2me | Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_normd
-- name    : GlobalTheory.UT.SymFrame.GRep.normd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:58:45.227071+00:00
-- url     : https://prove2.me/theorems/249dc900-6203-4cb6-9b10-f14781ec429b
-- title:
--   GRep: normd
-- statement:
--   The GRep construction uses the normd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UnivIdentity.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UnivIdentity.lean#L99-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}

theorem GlobalTheory.UT.SymFrame.GRep.normd {P v} (h : GRep D.P.L D.P.A P v) {K : Type} [Fintype K] (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ)
    (hP : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), P U h = ∏ k, h (φ k) ^ ε k)
    (h₁ : ∀ y J, Good D.P.L y J → v (𝟙_ _) 1 y J = 1) :
    ∃ s : LB.Gen (LB.LinComb D.P.L φ ε), Normd s ∧ ∀ (T : Over _) (r : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
      val s r.left z J = v T r z J := by sorry
