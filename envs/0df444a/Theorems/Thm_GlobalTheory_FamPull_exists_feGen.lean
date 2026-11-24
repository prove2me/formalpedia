-- Prove2me | Theorems.Thm_GlobalTheory_FamPull_exists_feGen
-- name    : GlobalTheory.FamPull.exists_feGen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:19:20.192883+00:00
-- url     : https://prove2.me/theorems/248d2ab4-9a43-4f39-a238-7ba7a66dbd91
-- title:
--   Fam Pull: exists fe Gen
-- statement:
--   The Fam Pull construction uses the exists fe Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L108-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L108-L149

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
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
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem GlobalTheory.FamPull.exists_feGen (ψW : PsiOn D W) (k : ℕ) (mu α : D.X) :
    ∃ (K : Type) (_ : Fintype K) (φ : K → ((TW W ⊗ D.P.A).left ⟶ D.P.A.left)) (ε : K → ℤ)
      (u : LB.Gen (LB.LinComb D.P.L φ ε)), u.IsGen ∧
      FormEq (Sum.elim (fun i => (snd (TW W) D.P.A * cP D _ mu).left ≫ D.famφB α i) φ) (Sum.elim (DegPre.famε k) ε)
        (fun i => (snd (TW W) D.P.A).left ≫ D.famφB (α + k • mu) i) (DegPre.famε k) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TW W ⊗ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = feUnit D k mu α (ρ ≫ snd _ _) z J (fun χ => val (ψW.psi χ) (ρ ≫ fst _ _).left z J)
          (val (D.rigW W) (ρ ≫ fst _ _).left z J) := by sorry
