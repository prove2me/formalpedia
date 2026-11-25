-- Prove2me | Theorems.Thm_GlobalTheory_WitnessData_exists_isPullDeg_pre
-- name    : GlobalTheory.WitnessData.exists_isPullDeg_pre
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:30.493832+00:00
-- url     : https://prove2.me/theorems/21e0da46-5d5f-4805-bfbb-066dbf9a30d7
-- title:
--   Witness Data: exists is Pull Deg pre
-- statement:
--   The Witness Data construction uses the exists is Pull Deg pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataIsoOfTwoWitnesses.lean#L102-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataIsoOfTwoWitnesses.lean#L102-L172

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

theorem GlobalTheory.WitnessData.exists_isPullDeg_pre {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] {f : O' →+* R}
    {D₀ : DegPre O'} {D D' : DegPre R} {φ : D.P.A.left ⟶ D₀.P.A.left} {φ' : D'.P.A.left ⟶ D₀.P.A.left}
    (he : eSec D.P.A ≫ φ = spMap f ≫ eSec D₀.P.A) (he' : eSec D'.P.A ≫ φ' = spMap f ≫ eSec D₀.P.A)
    {w : LB.Iso D.P.L (D₀.P.L.pull φ)} {w' : LB.Iso D'.P.L (D₀.P.L.pull φ')} (ε : D₀.X ≃+ D.X) (ε' : D₀.X ≃+ D'.X)
    (s1 : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (s1' : IsGrpPullback D'.P.A D₀.P.A (spMap f) φ')
    (s2 : w.IsGen) (s2' : w'.IsGen)
    (s3 : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1)) D.rig
      (rigPullOf φ (spMap f) he D₀.P.L D₀.rig))
    (s3' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf φ' (spMap f) he' D₀.P.L D₀.rig))
    (s5 : ∀ y, (D.c (ε y)).left ≫ φ = spMap f ≫ (D₀.c y).left)
    (s5' : ∀ y, (D'.c (ε' y)).left ≫ φ' = spMap f ≫ (D₀.c y).left)
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (v : D₀.X → F)
    (k : ∀ y, GenRel w (LB.pullGen _ _ _ (D.psi (ε y)) (jFK (R := R) F))
      (LB.pullGen _ _ _ (D₀.psi y) (jFK (R := O') F)) (v y))
    (k' : ∀ y, GenRel w' (LB.pullGen _ _ _ (D'.psi (ε' y)) (jFK (R := R) F))
      (LB.pullGen _ _ _ (D₀.psi y) (jFK (R := O') F)) (v y))
    {Wo : (Spec (CommRingCat.of R)).Opens} (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) (ψW : PsiOn D Wo) :
    ∃ hD : IsPullDeg (RingHom.id R) D D', (∀ y, hD.xe (ε' y) = ε y) ∧
      ∃ w'' : LB.Iso D'.P.L (D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ)),
        φ' = (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ ∧ HEq w' w'' ∧ Tri w hD.w w'' := by sorry
