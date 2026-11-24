-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_cut_out_subalgebra_quasiCoherent
-- name    : GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:32.547365+00:00
-- url     : https://prove2.me/theorems/bb9da80b-e3ab-40f3-930d-c662de571679
-- title:
--   T: finite cut out subalgebra quasi Coherent
-- statement:
--   The T construction uses the finite cut out subalgebra quasi Coherent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteCutOutSubalgebraQuasiCoherentStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteCutOutSubalgebraQuasiCoherentStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteCutOutSubalgebraQuasiCoherent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubmoduleFgOfLocallyLeFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgLocalizationAwaySpanFinsetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteCutOutSubalgebraQuasiCoherentStatement
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

theorem GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral) → ∀ {ι : Type} (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → (∀ x : X, ∃ j, x ∈ V j) → ∀ (T : ∀ j, Set (F.obj (op (V j)))), (∀ j, (T j).Finite) → ∀ W : X.Opens, IsAffineOpen W → (subMap F α V T W).Finite := by sorry
