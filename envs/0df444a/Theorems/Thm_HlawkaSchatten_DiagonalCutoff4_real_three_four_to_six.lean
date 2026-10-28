-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_four_to_six
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_four_to_six
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T00:45:13.948488+00:00
-- url     : https://prove2.me/theorems/ef250dcd-b74c-4162-aadf-1f68c353d915
-- title:
--   The remaining real three-dimensional Hlawka interval [4,6]
-- statement:
--   For every real $p\in[4,6]$ and $x,y,z\in\mathbb R^3$, let $S=\|x\|_p+\|y\|_p+\|z\|_p$, $T=\|x+y+z\|_p$, and $P=\|x+y\|_p+\|x+z\|_p+\|y+z\|_p$. With the unchanged campaign cyclic constant $K_p$, prove
--   $$S-T\le K_p(2S-P).$$
--   This interval remains open. It is the missing admissibility step for the proposed cutoff-four extension; partial localization certificates and proved analytic tools do not yet constitute a complete proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . The cutoff-six theorem is proved: https://prove2.me/theorems/cc454546-564a-4781-a821-e78176963c44 . The extension to cutoff four is work in progress; the finite interval is not yet proved.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_three_four_to_six :
    ∀ p : ℝ, 4 ≤ p → p ≤ 6 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
