-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_exists_of_succ
-- name    : GlobalTheory.FinEt.IsSplitOfRank.exists_of_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:07.748122+00:00
-- url     : https://prove2.me/theorems/8545c439-b032-4bfc-8ce0-3f830f48a6cb
-- title:
--   Is Split Of Rank: exists of succ
-- statement:
--   The Is Split Of Rank construction uses the exists of succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L492-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L492-L532

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

theorem GlobalTheory.FinEt.IsSplitOfRank.exists_of_succ {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ}
    (h : IsSplitOfRank p (n + 1)) :
    ∃ (σ : S ⟶ X) (_ : IsOpenImmersion σ) (V : X.Opens), σ ≫ p = 𝟙 S ∧
      Set.range V.ι = (Set.range σ)ᶜ ∧ IsSplitOfRank (V.ι ≫ p) n := by sorry
