-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff_exists_iso
-- name    : GlobalTheory.FinEt.isSplitOfRank_iff_exists_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:06.835127+00:00
-- url     : https://prove2.me/theorems/29087398-4d29-46ec-9992-ee176767459f
-- title:
--   Fin Et: is Split Of Rank iff exists iso
-- statement:
--   The Fin Et construction uses the is Split Of Rank iff exists iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L371-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L371-L385

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

theorem GlobalTheory.FinEt.isSplitOfRank_iff_exists_iso {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ) :
    IsSplitOfRank p n ↔
      ∃ e : (∐ fun _ : Fin n ↦ S) ≅ X, e.hom ≫ p = Sigma.desc fun _ : Fin n ↦ 𝟙 S := by sorry
