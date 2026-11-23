-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_isPullback_section
-- name    : GlobalTheory.FinEt.isPullback_section
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:13.084526+00:00
-- url     : https://prove2.me/theorems/837a4d22-483e-4e72-8949-8b62dfeefd2e
-- title:
--   Fin Et: is Pullback section
-- statement:
--   The Fin Et construction uses the is Pullback section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L414-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L414-L419

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}

theorem GlobalTheory.FinEt.isPullback_section {X S X' S' : Scheme.{u}} {a : X' ⟶ X} {q : X' ⟶ S'} {p : X ⟶ S}
    {t : S' ⟶ S} (H : IsPullback a q p t) (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) :
    IsPullback (H.lift (t ≫ σ) (𝟙 S') (by simp [hσ])) t a σ := by sorry
