-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_cutoff6
-- name    : HlawkaSchatten.DiagonalCutoff6.cutoff6
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:33:26.774507+00:00
-- url     : https://prove2.me/theorems/cc454546-564a-4781-a821-e78176963c44
-- title:
--   The sharp diagonal Hlawka constant for every real exponent p >= 6
-- statement:
--   For every real $p\ge6$, define
--   $$K_p=\max_{1/2\le t\le2}\frac{3(t^p+2)^{1/p}-3^{1/p}|2-t|}{6(t^p+2)^{1/p}-3(2|1-t|^p+2^p)^{1/p}}.$$
--   Then $K_p$ is the least real constant $C$ such that
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\le C\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   for every finite dimension and every triple of complex vectors. This establishes cutoff 6 in the sharp diagonal Hlawka campaign. It does not assert that 6 is optimal.
-- source:
--   Sharp diagonal Hlawka campaign, https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Cutoff-six extension by signed-tail localization, certified on the adjoining interval [6,8], followed by the proved cutoff-eight theorem https://prove2.me/theorems/90469677-ca50-457a-9f9d-f2b8f931e526 .

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff6.cutoff6 :
    ∀ p : ℝ, 6 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
