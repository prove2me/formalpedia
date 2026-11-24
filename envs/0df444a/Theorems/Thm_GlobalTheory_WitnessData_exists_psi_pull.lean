-- Prove2me | Theorems.Thm_GlobalTheory_WitnessData_exists_psi_pull
-- name    : GlobalTheory.WitnessData.exists_psi_pull
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:37.629469+00:00
-- url     : https://prove2.me/theorems/86c4ce98-3849-4b63-884a-b36581327e03
-- title:
--   Witness Data: exists psi pull
-- statement:
--   The Witness Data construction uses the exists psi pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataIsoOfTwoWitnesses.lean#L48-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataIsoOfTwoWitnesses.lean#L48-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataIsoOfTwoWitnesses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WitnessData

theorem GlobalTheory.WitnessData.exists_psi_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {Φ : D'.P.A.left ⟶ D.P.A.left}
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W)
    {g : (TK R).left ⟶ (TW W).left} (hg : g ≫ W.ι = jK R) {x : D'.X} {y : D.X} (hx : D'.xK x ≫ Φ = D.xK y)
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (H : ∀ (z : Sp F) (p : D.P.L.ι) (q : D'.P.L.ι), Φ (D'.xK x (jFK (R := R) F z)) ∈ D.P.L.U p →
      D'.xK x (jFK (R := R) F z) ∈ D'.P.L.U q →
      gm (jFK (R := R) F) z (LB.wchart D.P.L (fun _ : PUnit => D.xK y) (fun _ => p)) ((D.psi y).s (fun _ => p)) =
        gw w (jFK (R := R) F ≫ D'.xK x) z p q ^ (-1 : ℤ) *
          gm (jFK (R := R) F) z (LB.wchart D'.P.L (fun _ : PUnit => D'.xK x) (fun _ => q)) ((D'.psi x).s (fun _ => q))) :
    ∃ b : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => D'.xK x ≫ Φ) (fun _ => -1)),
      GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit) (fun _ => Φ) w (D'.xK x) (-1) (D'.psi x) b ∧
      LB.Gen.Corr D.P.L _ _ _ _ b (LB.pullGen D.P.L _ _ (ψW.psi y) g) := by sorry
