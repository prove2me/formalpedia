-- Prove2me | Theorems.Thm_GlobalTheory_SS_OrdProd_jac_block
-- name    : GlobalTheory.SS.OrdProd.jac_block
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:31:16.615071+00:00
-- url     : https://prove2.me/theorems/f55a1bae-85d4-459a-b578-f359414c95e5
-- title:
--   Ord Prod: jac block
-- statement:
--   The Ord Prod construction uses the jac block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VectorFieldOrderAddOfProdStrictHenselian.lean#L167-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VectorFieldOrderAddOfProdStrictHenselian.lean#L167-L182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsEqDivOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsVf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdProd
variable {K : Type} [Field K]

theorem GlobalTheory.SS.OrdProd.jac_block {P X Y : Over (Sp K)} {p : P ⟶ X} {q : P ⟶ Y} {I I' : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] {D : I → VF X} {D' : I' → VF Y} {E : I ⊕ I' → VF P}
    (a₁ : ∀ i, Lifts p (E (.inl i)) (D i)) (a₂ : ∀ i, Lifts q (E (.inl i)) (VF.zero Y))
    (b₁ : ∀ i, Lifts q (E (.inr i)) (D' i)) (b₂ : ∀ i, Lifts p (E (.inr i)) (VF.zero X))
    (V : X.left.Opens) (V' : Y.left.Opens) (W : P.left.Opens) (h : W ≤ p.left ⁻¹ᵁ V) (h' : W ≤ q.left ⁻¹ᵁ V')
    (t : I → Γ(X.left, V)) (t' : I' → Γ(Y.left, V')) :
    jac E W (Sum.elim (fun i => (p.left.appLE V W h).hom (t i)) fun i => (q.left.appLE V' W h').hom (t' i)) =
      (p.left.appLE V W h).hom (jac D V t) * (q.left.appLE V' W h').hom (jac D' V' t') := by sorry
