-- Prove2me | Theorems.Thm_GlobalTheory_UnitBallBasis_exists_basis_mem_iff_norm_le_one
-- name    : GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:25:20.220895+00:00
-- url     : https://prove2.me/theorems/eec9fe89-ea16-41d6-9cc3-9e786da39b83
-- title:
--   Unit Ball Basis: exists basis mem iff norm le one
-- statement:
--   The Unit Ball Basis construction uses the exists basis mem iff norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBasisMemIffNormLeOne.lean#L5-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBasisMemIffNormLeOne.lean#L5-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisMemIffNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitBallBasis

theorem GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one {l : ℕ} [inst : Fact (Nat.Prime l)] {L O V : Type}
    [inst_1 : Field L] [inst_2 : Algebra ℚ_[l] L] [inst_3 : CommRing O] [inst_4 : Algebra O L]
    [inst_5 : Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (hc : ∀ (a : ℤ_[l]), algebraMap O L (algebraMap ℤ_[l] O a) = algebraMap ℚ_[l] L (a : ℚ_[l]))
    (hd : ∀ (a : L), ∃ (y : ℤ_[l]), y ≠ 0 ∧ ∃ (o : O),
      algebraMap O L o = algebraMap ℚ_[l] L (y : ℚ_[l]) * a)
    [inst_8 : AddCommGroup V] [inst_9 : Module L V] [inst_10 : Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] L V] [inst_12 : Module O V] [IsScalarTower O L V]
    (S : Submodule O V) (hfg : S.FG) (hfree : Module.Free O S)
    (hspan : Submodule.span L (S : Set V) = ⊤) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ (x : V),
      x ∈ S ↔ ∀ (i : Fin n), ‖w.repr x i‖ ≤ (1 : ℝ) := by sorry
