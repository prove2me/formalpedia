-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_subMap_finite
-- name    : GlobalTheory.QcSub.subMap_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:03:41.452901+00:00
-- url     : https://prove2.me/theorems/b3ed049f-645c-432a-a9d9-c3ca249f5789
-- title:
--   Qc Sub: sub Map finite
-- statement:
--   The Qc Sub construction uses the sub Map finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteCutOutSubalgebraQuasiCoherent.lean#L10-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteCutOutSubalgebraQuasiCoherent.lean#L10-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubmoduleFgOfLocallyLeFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgLocalizationAwaySpanFinsetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteCutOutSubalgebraQuasiCoherent
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

theorem GlobalTheory.QcSub.subMap_finite (X : Scheme.{0}) (_hX : IsNoetherian X) (F : X.Opensᵒᵖ ⥤ CommRingCat)
    (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (hint : ∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral)
    {ι : Type} (V : ι → X.Opens) (_hV : ∀ j, IsAffineOpen (V j)) (hcov : ∀ x : X, ∃ j, x ∈ V j)
    (T : ∀ j, Set (F.obj (op (V j)))) (hT : ∀ j, (T j).Finite) (W : X.Opens)
    (hW : IsAffineOpen W) : (subMap F α V T W).Finite := by sorry
