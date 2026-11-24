-- Prove2me | Theorems.Thm_GlobalTheory_T_coequifibered_generated_subalgebra_quasiCoherent
-- name    : GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:30:24.951054+00:00
-- url     : https://prove2.me/theorems/a7006fbd-ceb9-48b9-8ea0-f388874708a0
-- title:
--   T: coequifibered generated subalgebra quasi Coherent
-- statement:
--   The T construction uses the coequifibered generated subalgebra quasi Coherent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoequifiberedGeneratedSubalgebraQuasiCoherentStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoequifiberedGeneratedSubalgebraQuasiCoherentStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoequifiberedGeneratedSubalgebraQuasiCoherent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoequifiberedGeneratedSubalgebraQuasiCoherentStatement
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

theorem GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j)))), (∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) → (subNat F α V T).Coequifibered := by sorry
