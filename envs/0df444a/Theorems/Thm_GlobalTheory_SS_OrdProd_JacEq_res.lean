-- Prove2me | Theorems.Thm_GlobalTheory_SS_OrdProd_JacEq_res
-- name    : GlobalTheory.SS.OrdProd.JacEq.res
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:30:50.807353+00:00
-- url     : https://prove2.me/theorems/5248f149-be8b-4e49-ac07-a631ceade672
-- title:
--   Jac Eq: res
-- statement:
--   The Jac Eq construction uses the res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VectorFieldOrderAddOfProdStrictHenselian.lean#L271-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VectorFieldOrderAddOfProdStrictHenselian.lean#L271-L277

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
variable {R : Type} [CommRing R] [Algebra R K] {A A' : Over (Sp K)}

theorem GlobalTheory.SS.OrdProd.JacEq.res {I : Type} [Fintype I] [DecidableEq I] {M : Model R A} {D : I → VF A} {c : K}
    {U V : M.Y.left.Opens} {t : I → Γ(M.Y.left, U)} {s : Γ(M.Y.left, U)} (H : JacEq M D c U t s) (h : V ≤ U) :
    JacEq M D c V (fun i => (M.Y.left.presheaf.map (homOfLE h).op).hom (t i))
      ((M.Y.left.presheaf.map (homOfLE h).op).hom s) := by sorry
