-- Prove2me | Theorems.Thm_GlobalTheory_AlgClosedFibre_exists_point_mem_translates
-- name    : GlobalTheory.AlgClosedFibre.exists_point_mem_translates
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:56:19.009388+00:00
-- url     : https://prove2.me/theorems/0736d48f-498a-4249-bcad-fcd6cb7817aa
-- title:
--   Alg Closed Fibre: exists point mem translates
-- statement:
--   The Alg Closed Fibre construction uses the exists point mem translates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPointMemTranslates.lean#L9-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPointMemTranslates.lean#L9-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPointMemTranslates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AlgClosedFibre

theorem GlobalTheory.AlgClosedFibre.exists_point_mem_translates :
    ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens),
      (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)),
      ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧
        (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by sorry
