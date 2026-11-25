-- Prove2me | Theorems.Thm_GlobalTheory_TauPull_val_tauW
-- name    : GlobalTheory.TauPull.val_tauW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:16.955189+00:00
-- url     : https://prove2.me/theorems/27f5661a-ac6b-4295-9709-92a6d2cf76aa
-- title:
--   Tau Pull: val tau W
-- statement:
--   The Tau Pull construction uses the val tau W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultOfIsPullDeg.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultOfIsPullDeg.lean#L77-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem GlobalTheory.TauPull.val_tauW (ψW : PsiOn D W) {Z : Scheme.{0}} (r : Z ⟶ (TW W).left) {z : Z} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val (ψW.tau a b) r z J =
      val (ψW.psi (a + b)) r z J * (val (ψW.psi a) r z J)⁻¹ * (val (ψW.psi b) r z J)⁻¹ * (val (D.rigW W) r z J)⁻¹ := by sorry
