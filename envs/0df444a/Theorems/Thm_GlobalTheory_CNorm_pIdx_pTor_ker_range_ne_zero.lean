-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_pIdx_pTor_ker_range_ne_zero
-- name    : GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:51.212979+00:00
-- url     : https://prove2.me/theorems/2776cc8a-7e64-4786-bb6e-650303394fb3
-- title:
--   CNorm: p Idx p Tor ker range ne zero
-- statement:
--   The CNorm construction uses the p Idx p Tor ker range ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowIndexTorsionFiniteKerRange.lean#L8-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowIndexTorsionFiniteKerRange.lean#L8-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionFiniteKerRange
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

theorem GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero :
    ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'),
      pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → pTor p g.range ≠ 0 →
      pIdx p g.ker ≠ 0 ∧ pTor p g.ker ≠ 0 ∧ pIdx p g.range ≠ 0 := by sorry
