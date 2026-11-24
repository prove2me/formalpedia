-- Prove2me | Theorems.Thm_GlobalTheory_SS_Ord_jac_mem_basicOpen
-- name    : GlobalTheory.SS.Ord.jac_mem_basicOpen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:16:48.70643+00:00
-- url     : https://prove2.me/theorems/52cbb763-8868-4142-9c26-284bec7aa8bd
-- title:
--   Ord: jac mem basic Open
-- statement:
--   The Ord construction uses the jac mem basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L378-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L378-L392

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem GlobalTheory.SS.Ord.jac_mem_basicOpen (M : Model R A) (D : I → VF A) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    (g : Γ(M.Y.left, U)) (N : AddSubgroup Γ(A.left, M.j ⁻¹ᵁ M.Y.left.basicOpen g))
    (hN : ∀ s, ∀ x ∈ N, (M.j.app (M.Y.left.basicOpen g)).hom s * x ∈ N)
    (h : ∀ t : I → Γ(M.Y.left, U), rs _ (M.j.preimage_mono (M.Y.left.basicOpen_le g))
      (jac D (M.j ⁻¹ᵁ U) fun i => (M.j.app U).hom (t i)) ∈ N) (t : I → Γ(M.Y.left, M.Y.left.basicOpen g)) :
    jac D _ (fun i => (M.j.app (M.Y.left.basicOpen g)).hom (t i)) ∈ N := by sorry
