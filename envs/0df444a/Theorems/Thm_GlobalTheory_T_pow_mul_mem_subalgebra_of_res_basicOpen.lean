-- Prove2me | Theorems.Thm_GlobalTheory_T_pow_mul_mem_subalgebra_of_res_basicOpen
-- name    : GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:55:17.569287+00:00
-- url     : https://prove2.me/theorems/cb26cc16-207f-455e-a832-73934581fcda
-- title:
--   T: pow mul mem subalgebra of res basic Open
-- statement:
--   The T construction uses the pow mul mem subalgebra of res basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowMulMemSubalgebraOfResBasicOpenStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowMulMemSubalgebraOfResBasicOpenStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulMemSubalgebraOfResBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowMulMemAdjoinOfLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulMemSubalgebraOfResBasicOpenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by sorry
