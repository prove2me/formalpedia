-- Prove2me | Theorems.Thm_GlobalTheory_FamPull_famFE_iff
-- name    : GlobalTheory.FamPull.famFE_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:37.962967+00:00
-- url     : https://prove2.me/theorems/1311c1cd-2e28-4d17-bb1f-f680dd534a76
-- title:
--   Fam Pull: fam FE iff
-- statement:
--   The Fam Pull construction uses the fam FE iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L79-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L79-L100

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
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.FamPull.famFE_iff (hG : GlobalFnsSt) {k : ℕ} (s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (f : ∀ α, D.SecB k α) (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s α) (D.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D F).left 1) :
    DegPre.FamFE D F k s ↔ ∀ (mu α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J),
      Good D.P.L z J → sval (f (α + k • mu)) (ρ ≫ DegPre.prB D F).left z J =
        sval (f α) ((ρ ≫ DegPre.prB D F) * cP D T mu).left z J *
          (feUnit D k mu α (ρ ≫ DegPre.prB D F) z J
            (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
            (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)).val := by sorry
