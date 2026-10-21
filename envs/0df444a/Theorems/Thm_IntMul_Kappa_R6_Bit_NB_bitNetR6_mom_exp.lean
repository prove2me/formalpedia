-- Prove2me | Theorems.Thm_IntMul_Kappa_R6_Bit_NB_bitNetR6_mom_exp
-- name    : IntMul.Kappa.R6.Bit.NB.bitNetR6_mom_exp
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-20T21:04:35.685399+00:00
-- url     : https://prove2.me/theorems/e810e824-0d98-4b94-84eb-5da5b49324f8
-- title:
--   Round-six bit network, moment statement unfolded
-- statement:
--   The round-six bit-network moment statement `IntMul.Kappa.R6.Bit.BitNetR6MomStmt` with its definition unfolded: there is a QH-network over ZMod 2 of size 148225616 and width 529 that runs correctly, whose edge and formal checks hold for all large prime powers, and whose child-width histogram moments are bounded by those of `Jain.bitR6` for every τ in (0, 1].
--
--   This node exists because two published bundles (`IntMul_Kappa_R6_Defs16` and `IntMul_Kappa_R6_Defs52`) both contain `BitNetR6MomStmt` and cannot be imported together; the statement here mentions only shared definitions, so the final round-six assembly can use the bit network.
--
--   ```lean
--   theorem IntMul.Kappa.R6.Bit.NB.bitNetR6_mom_exp :
--     ∃ (T : ℕ) (C : QHNet (ZMod 2) 148225616 T 529) (q₀ : ℕ), C.RunsOK ∧
--       (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
--       ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment C.hist 529 τ ≤ histMoment Jain.bitR6 529 τ
--   ```
-- source:
--   S. Jain, round-six networks for the integer-multiplication κ-improvement campaign (https://github.com/Swapnil-jain/integer-mult-kappa, commit 5868dc7); target `IntMul.Kappa.jain_round6_framework`. Bridge restating `IntMul.Kappa.R6.Bit.NB.bitNetR6_mom` (theorem 6d4ae477-d517-42ab-acc2-a50ca24c517c).

-- Round-six κ development (integer-multiplication-kappa): bridge for the bit-network moment statement.

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R6_Defs4

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul IntMul.Kappa IntMul.Kappa.R6 IntMul.Kappa.R6.Bit

theorem IntMul.Kappa.R6.Bit.NB.bitNetR6_mom_exp :
  ∃ (T : ℕ) (C : QHNet (ZMod 2) 148225616 T 529) (q₀ : ℕ), C.RunsOK ∧
    (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 → histMoment C.hist 529 τ ≤ histMoment Jain.bitR6 529 τ := by sorry
