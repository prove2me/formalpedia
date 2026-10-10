-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_local_failure62
-- name    : HlawkaSchatten.DiagonalCutoff.local_failure62
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T07:38:37.138778+00:00
-- url     : https://prove2.me/theorems/8567da26-aee2-4a37-896a-993adb0864ba
-- title:
--   A negative deficit localizes into the cutoff-62 entry box
-- statement:
--   If the cyclic constant exceeds both $\frac{23}{50}p$ and the scalar envelope at $\frac{3643}{10000}$, then any real three-coordinate counterexample to the cyclic bound can be rotated and signed into a fixed asymmetric box on which the triple deficit is still negative.
--
--   Let $p\ge 62$, and assume $\frac{23}{50}p < C(p)$ and $E(p,\frac{3643}{10000}) < C(p)$. If the Hlawka deficit of three real vectors at height $C(p)$ is negative, there is a $3\times 3$ real matrix $X$ with negative triple deficit whose entries obey
--   $$
--   -\frac{10929}{10000}\le X_{jj}\le -\frac{28719}{38750},\qquad
--   \frac{28719}{38750}\le X_{ji}\le \frac{10929}{10000}\ (i\ne j).
--   $$
--
--   The lower entry $\frac{28719}{38750}$ is the frozen left endpoint of the cutoff-$62$ confinement at radius $\frac{3643}{10000}$.
--
--   **Formalization Note.** The box is the set comprehension in `local_failure62`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — localization of a negative cyclic deficit into the cutoff-62 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.local_failure62 : ∀ p : ℝ, 62 ≤ p →
    (23 / 50 : ℝ) * p < cyclicConstant p →
    scalarEnvelope p (3643 / 10000) < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ ({X : Triple | ∀ j i,
          if j = i then -(10929 / 10000 : ℝ) ≤ X j i ∧ X j i ≤ -(28719 / 38750 : ℝ)
          else (28719 / 38750 : ℝ) ≤ X j i ∧ X j i ≤ (10929 / 10000 : ℝ)} : Set Triple),
          tripleDeficit p (cyclicConstant p) X < 0 := by sorry
