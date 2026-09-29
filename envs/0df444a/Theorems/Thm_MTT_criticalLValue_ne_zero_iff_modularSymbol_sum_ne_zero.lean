-- Prove2me | Theorems.Thm_MTT_criticalLValue_ne_zero_iff_modularSymbol_sum_ne_zero
-- name    : MTT.criticalLValue_ne_zero_iff_modularSymbol_sum_ne_zero
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-23T06:55:31.982679+00:00
-- url     : https://prove2.me/theorems/fee1cc71-6da8-4eb7-aa86-c122abb63bb5
-- title:
--   Birch--Mellin detects nonvanishing
-- statement:
--   For a primitive Dirichlet character, the scalar in the Birch--Mellin formula is nonzero: the factorial, conductor, powers of 2πi, and primitive Gauss sum are all nonzero. Hence the critical L-value is nonzero exactly when the character-weighted modular-symbol sum is nonzero.
-- source:
--   Kriz--Nordentoft, https://arxiv.org/pdf/2310.20678, Corollary 3.6 and Corollary 5.4; MTT.birch_mellin_formula.

import Theorems.Thm_MTT_birch_mellin_formula

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
/-- For a primitive Dirichlet character, the scalar in the Birch--Mellin
formula is nonzero.  Thus the critical L-value vanishes exactly when its
character-weighted modular-symbol sum vanishes. -/
theorem MTT.criticalLValue_ne_zero_iff_modularSymbol_sum_ne_zero
    {N k m : ℕ} [NeZero m] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι)
    (χ : DirichletCharacter Qbar m) (hχ : χ.IsPrimitive)
    (j : ℕ) (hj : j ≤ k - 2) :
    criticalLValue ι f.form m χ j ≠ 0 ↔
      (∑ a : ZMod m, ι (χ a) * modularSymbol f.form j a.val m) ≠ 0 := by
  sorry
