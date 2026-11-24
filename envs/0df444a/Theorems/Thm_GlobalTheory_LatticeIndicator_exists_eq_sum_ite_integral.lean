-- Prove2me | Theorems.Thm_GlobalTheory_LatticeIndicator_exists_eq_sum_ite_integral
-- name    : GlobalTheory.LatticeIndicator.exists_eq_sum_ite_integral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:59:59.214946+00:00
-- url     : https://prove2.me/theorems/06da4416-1cee-4f3b-990e-3ef01901ba95
-- title:
--   Lattice Indicator: exists eq sum ite integral
-- statement:
--   The Lattice Indicator construction uses the exists eq sum ite integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L248-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L248-L286

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
open Classical

theorem GlobalTheory.LatticeIndicator.exists_eq_sum_ite_integral {O m n R : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [CommRing R] {c : O} (hc : c ≠ 0) (ψ : Matrix m n O → R)
    (hinv : ∀ (z : Matrix m n O) (k : GL n O), ψ (z * (k : Matrix n n O)) = ψ z)
    (hper : ∀ z y : Matrix m n O, ψ (z + c • y) = ψ z) :
    ∃ (r : ℕ) (h : Fin r → Matrix m m O) (a : Fin r → R), (∀ l, (h l).det ≠ 0) ∧
      ∀ z, ψ z = ∑ l, a l * (if ∃ y : Matrix m n O, z = h l * y then 1 else 0) := by sorry
