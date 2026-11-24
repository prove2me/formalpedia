-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finite_coequifibered_subalgebra_alt
-- name    : GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:36:04.811913+00:00
-- url     : https://prove2.me/theorems/84d400a4-114b-4e3e-bb87-4311515f1679
-- title:
--   T: exists finite coequifibered subalgebra alt
-- statement:
--   The T construction uses the exists finite coequifibered subalgebra alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCoequifiberedSubalgebraStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCoequifiberedSubalgebraStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCoequifiberedSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCoequifiberedSubalgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by sorry
