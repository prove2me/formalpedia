-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_pIdx_top_of_fg
-- name    : GlobalTheory.CNorm.pIdx_top_of_fg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:37.332687+00:00
-- url     : https://prove2.me/theorems/c08ff1ee-2750-4bd4-ad5d-41a7b028cea3
-- title:
--   CNorm: p Idx top of fg
-- statement:
--   The CNorm construction uses the p Idx top of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowRelIndexTopOfGroupFg.lean#L90-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowRelIndexTopOfGroupFg.lean#L90-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexTopOfGroupFg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped WithZero TensorProduct

theorem GlobalTheory.CNorm.pIdx_top_of_fg : ∀ (p : ℕ) (G : Type) [CommGroup G] [Group.FG G],
    0 < p →
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) ≠ 0 ∧
      _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup G) =
        p ^ Module.finrank ℤ (Additive G) * _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) := by sorry
