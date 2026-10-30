-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_cutoff4
-- name    : HlawkaSchatten.DiagonalCutoff4.cutoff4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T00:45:11.554737+00:00
-- url     : https://prove2.me/theorems/0ee0074e-f0be-4d07-89a9-f8012acf0199
-- title:
--   The sharp diagonal Hlawka constant for every real exponent p >= 4
-- statement:
--   For every real $p\ge4$, define the unchanged cyclic constant
--   $$K_p=\max_{1/2\le t\le2}\frac{3(t^p+2)^{1/p}-3^{1/p}|2-t|}{6(t^p+2)^{1/p}-3(2|1-t|^p+2^p)^{1/p}}.$$
--   Prove that $K_p$ is the least real constant $C$ such that
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\le C\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   for every finite dimension and all complex vectors $x,y,z$ in that dimension.
--   This theorem is proved on Prove2Me. The complete real three-dimensional interval $[4,6]$, the campaign reductions, and the proved cutoff-six theorem establish the result for every $p\ge4$. Four is not asserted to be the optimal cutoff.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . The real interval [4,6] is proved: https://prove2.me/theorems/ef250dcd-b74c-4162-aadf-1f68c353d915 . The proved cutoff-six theorem covers p >= 6: https://prove2.me/theorems/cc454546-564a-4781-a821-e78176963c44 .

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.cutoff4 :
    ∀ p : ℝ, 4 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
