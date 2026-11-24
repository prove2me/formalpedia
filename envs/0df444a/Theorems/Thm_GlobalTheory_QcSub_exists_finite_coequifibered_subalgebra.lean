-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_exists_finite_coequifibered_subalgebra
-- name    : GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:23:04.601814+00:00
-- url     : https://prove2.me/theorems/019b34b0-faa1-4e62-a0ba-8cca3cb0fa10
-- title:
--   Qc Sub: exists finite coequifibered subalgebra
-- statement:
--   The Qc Sub construction uses the exists finite coequifibered subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCoequifiberedSubalgebra.lean#L12-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCoequifiberedSubalgebra.lean#L12-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulMemSubalgebraOfResBasicOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteCutOutSubalgebraQuasiCoherentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSetsSubalgebraFiniteAffineCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoequifiberedGeneratedSubalgebraQuasiCoherentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCoequifiberedSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
open GlobalTheory GlobalTheory.QcSub

theorem GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by sorry
