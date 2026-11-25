-- Prove2me | Theorems.Thm_GlobalTheory_UU_ExpLin_expT_linear
-- name    : GlobalTheory.UU.ExpLin.expT_linear
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:29:00.659856+00:00
-- url     : https://prove2.me/theorems/a48c6ac8-0792-4176-a82a-bf6cc219bccc
-- title:
--   Exp Lin: exp T linear
-- statement:
--   The Exp Lin construction uses the exp T linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalSecComb.lean#L43-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalSecComb.lean#L43-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalSecComb
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ExpLin

theorem GlobalTheory.UU.ExpLin.expT_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k n : ℕ) (c : Fin n → Γ(T.left, ⊤)) (σ : Fin n → U.SecGT T k) (f : Fin n → ∀ α, SecBT D T k α), (∀ i, U.ExpT T k (σ i) (f i)) → ∃ (σ' : U.SecGT T k) (f' : ∀ α, SecBT D T k α), U.ExpT T k σ' f' ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ' r z J = ∑ i, gs (r ≫ (fst T G).left) z ⊤ (c i) * sval (σ i) r z J) ∧ ∀ α (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J → sval (f' α) r z J = ∑ i, gs (r ≫ (fst T D.P.A).left) z ⊤ (c i) * sval (f i α) r z J := by sorry
