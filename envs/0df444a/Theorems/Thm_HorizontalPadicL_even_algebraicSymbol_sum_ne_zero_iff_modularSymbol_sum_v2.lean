-- Prove2me | Theorems.Thm_HorizontalPadicL_even_algebraicSymbol_sum_ne_zero_iff_modularSymbol_sum_v2
-- name    : HorizontalPadicL.even_algebraicSymbol_sum_ne_zero_iff_modularSymbol_sum_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:29:31.859676+00:00
-- url     : https://prove2.me/theorems/7a63de00-c47a-43f6-baa4-4e0a115a598e
-- title:
--   The central signed algebraic-symbol sum has the ordinary modular-symbol zero set
-- statement:
--   Period comparison converts the algebraic-symbol sum to a signed complex modular-symbol sum. For an even character, reindexing by a maps to -a and the selected central sign turn this signed sum into the ordinary modular-symbol sum without changing its zero set.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Corollary 3.6 and Corollary 5.4; standard Dirichlet-character and modular-symbol identities.

import Definitions.Def_KN_SeededInverseThetaSystemV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- For an even Dirichlet character and the central sign selected by the
inverse-seed theta construction, period comparison identifies the zero set of
the algebraic-symbol sum with that of the ordinary complex modular-symbol sum. -/
theorem even_algebraicSymbol_sum_ne_zero_iff_modularSymbol_sum_v2
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (hk : 2 ≤ k) (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form)
    (θ : DirichletCharacterWithLevel) (hθeven : θ.2 (-1) = 1)
    (s : Bool) (hs : (MTT.sign s : ℤ) = (-1 : ℤ) ^ (k / 2 - 1))
    (hcomparison : ∀ s j a m, j ≤ k - 2 → m ≠ 0 →
      ι (MTT.algebraicSymbol P s j a m) * P.omega s =
        signedModularSymbol f.form s j a m) :
    letI : NeZero θ.1.1 := ⟨Nat.ne_of_gt θ.1.2⟩
    ((∑ a : ZMod θ.1.1,
        θ.2 a * MTT.algebraicSymbol P s (k / 2 - 1) a.val θ.1.1) ≠ 0 ↔
      (∑ a : ZMod θ.1.1,
        ι (θ.2 a) * MTT.modularSymbol f.form
          (k / 2 - 1) a.val θ.1.1) ≠ 0) := by
  sorry

end HorizontalPadicL
