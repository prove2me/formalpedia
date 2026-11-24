-- Prove2me | Theorems.Thm_GlobalTheory_cayleyInv_skew
-- name    : GlobalTheory.cayleyInv_skew
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:50.591606+00:00
-- url     : https://prove2.me/theorems/91dc92f0-8b9f-438a-8732-c077ce66ff18
-- title:
--   Global Theory: cayley Inv skew
-- statement:
--   The Global Theory construction uses the cayley Inv skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryFamilyEqCayleyOfSkewFamily.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryFamilyEqCayleyOfSkewFamily.lean#L33-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory
variable {n : ℕ}

theorem GlobalTheory.cayleyInv_skew (X Z : Matrix (Fin n) (Fin n) ℂ) (hXZ : X * Zᵀ = 1)
    (hX : IsUnit (X + 1).det) (hZ : IsUnit (Z + 1).det) :
    (Z - 1) * (Z + 1)⁻¹ = -((X - 1) * (X + 1)⁻¹)ᵀ := by sorry
