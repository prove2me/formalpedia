-- Prove2me | Theorems.Thm_GlobalTheory_FamPull_val_feUnit
-- name    : GlobalTheory.FamPull.val_feUnit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:19:08.507977+00:00
-- url     : https://prove2.me/theorems/cfd084f9-97cd-4249-bf35-36f811d9d458
-- title:
--   Fam Pull: val fe Unit
-- statement:
--   The Fam Pull construction uses the val fe Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L67-L73

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

theorem GlobalTheory.FamPull.val_feUnit (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) {z : T.left} {J}
    (hJ : Good D.P.L z J) :
    uVal D F k α (cP D _ mu) ρ z J * val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J =
      feUnit D k mu α (ρ ≫ DegPre.prB D F) z J (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
        (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J) := by sorry
