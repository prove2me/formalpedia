-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_normOne_modEq_one_and_of_dvd
-- name    : GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:01.205663+00:00
-- url     : https://prove2.me/theorems/51d41be1-a8d8-40a4-9dff-86a12b21f2a5
-- title:
--   An: norm One mod Eq one and of dvd
-- statement:
--   The An construction uses the norm One mod Eq one and of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormOneModEqOneAndOfDvd.lean#L6-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormOneModEqOneAndOfDvd.lean#L6-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormOneModEqOneAndOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An

theorem GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd :
    ∀ d M p : ℕ, d % 4 = 3 → _root_.GlobalTheory.Mem.An.NormOne d M p →
      p ≡ 1 [MOD M] ∧ ∀ M' : ℕ, M' ∣ M → _root_.GlobalTheory.Mem.An.NormOne d M' p := by sorry
