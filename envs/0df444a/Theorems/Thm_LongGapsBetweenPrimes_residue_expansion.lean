-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_residue_expansion
-- name    : LongGapsBetweenPrimes.residue_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:26.535721+00:00
-- url     : https://prove2.me/theorems/ac43d66f-4359-4000-8e6c-af2966e310b7
-- title:
--   Long Gaps Between Primes: residue expansion
-- statement:
--   Expand a function of residues as a sum of residue indicators.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2288-L2291
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2288-L2291

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.residue_expansion {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (n : ℕ) :
    g ⟨n % m, Nat.mod_lt n hm⟩ = ∑ a : Fin m, g a * residueIndicator m a.val n := by sorry
