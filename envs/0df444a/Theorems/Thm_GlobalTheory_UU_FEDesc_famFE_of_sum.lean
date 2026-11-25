-- Prove2me | Theorems.Thm_GlobalTheory_UU_FEDesc_famFE_of_sum
-- name    : GlobalTheory.UU.FEDesc.famFE_of_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:27:02.741084+00:00
-- url     : https://prove2.me/theorems/434e785d-f1ee-5924-842c-e212b16a6223
-- title:
--   FEDesc: fam FE of sum
-- statement:
--   The FEDesc construction uses the fam FE of sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FiniteExponentBaseChangeField.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FiniteExponentBaseChangeField.lean#L38-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniquePullB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FamilyFunctionalEquationFieldChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFOfExpT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FiniteExponentBaseChangeField
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.FEDesc

theorem GlobalTheory.UU.FEDesc.famFE_of_sum {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k n : ℕ) (c : Fin n → F) (s : Raw D F k) (t : Fin n → Raw D F k)
    (h : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = ∑ i, gs r z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) * sval (t i α) r z J)
    (ht : ∀ i, DegPre.FamFE D F k (t i)) : DegPre.FamFE D F k s := by sorry
