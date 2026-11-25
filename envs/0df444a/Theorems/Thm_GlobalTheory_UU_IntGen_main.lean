-- Prove2me | Theorems.Thm_GlobalTheory_UU_IntGen_main
-- name    : GlobalTheory.UU.IntGen.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:36:32.559086+00:00
-- url     : https://prove2.me/theorems/93434791-98a9-5245-8982-3cd6890dd28b
-- title:
--   Int Gen: main
-- statement:
--   The Int Gen construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGenT.lean#L163-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGenT.lean#L163-L189

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
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
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.IntGen
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem GlobalTheory.UU.IntGen.main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α mu : D.X), ∃ (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k))) (r₁ r₂ : R), u₀.IsGen ∧ r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J → gs r z ⊤ (scal (DegPre.BF D F).hom r₂) * (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D F).hom r₁) * (val u₀ (r ≫ (φ ▷ D.P.A).left) z J).val := by sorry
