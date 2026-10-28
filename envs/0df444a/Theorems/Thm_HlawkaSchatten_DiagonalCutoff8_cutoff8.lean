-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_cutoff8
-- name    : HlawkaSchatten.DiagonalCutoff8.cutoff8
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T15:37:56.881541+00:00
-- url     : https://prove2.me/theorems/90469677-ca50-457a-9f9d-f2b8f931e526
-- title:
--   The sharp diagonal Hlawka constant for every real exponent p >= 8
-- statement:
--   For every real $p\ge8$, the cyclic constant
--   $$K_p=\max_{1/2\le t\le2}\frac{3(t^p+2)^{1/p}-3^{1/p}|2-t|}{6(t^p+2)^{1/p}-3(2|1-t|^p+2^p)^{1/p}}$$
--   is the least real constant $C$ such that
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\le C\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   for every finite dimension and every triple of complex vectors. The cutoff 8 is sufficient; this theorem does not assert it is optimal and does not settle exponents between 2 and 8.
-- source:
--   Cutoff-8 extension of the genuinely open sharp diagonal Hlawka campaign, https://prove2.me/theorems/7fe6f02d-65e5-4c21-9796-c83889b29b9d . Uses the adjoining [8,12] real-three-dimensional interval results, the proved cutoff-12 theorem, and the proved real-three-to-complex-sharpness transfer.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff8.cutoff8 :
    ∀ p : ℝ, 8 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
