-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_isLocalizationAway
-- name    : GlobalTheory.QcSub.isLocalizationAway
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:23.576271+00:00
-- url     : https://prove2.me/theorems/86c46b3d-1726-482b-ac92-1102a9fb44df
-- title:
--   Qc Sub: is Localization Away
-- statement:
--   The Qc Sub construction uses the is Localization Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L108-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L108-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite
open GlobalTheory GlobalTheory.QcSub
variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
variable {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))

theorem GlobalTheory.QcSub.isLocalizationAway
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W)) :
    letI := (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    IsLocalization.Away ((α.app (op W)).hom f) (F.obj (op (X.basicOpen f))) := by sorry
