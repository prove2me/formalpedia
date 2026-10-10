-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_local_failure63
-- name    : HlawkaSchatten.DiagonalCutoff.local_failure63
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T07:15:01.120216+00:00
-- url     : https://prove2.me/theorems/f9e8cbb8-1821-464f-bf37-63a38ead3177
-- title:
--   A negative deficit localizes into the cutoff-63 entry box
-- statement:
--   If the cyclic constant exceeds both $\frac{23}{50}p$ and the scalar envelope at $\frac{91}{250}$, then any real three-coordinate counterexample to the cyclic bound can be rotated and signed into a fixed asymmetric box on which the triple deficit is still negative.
--
--   Let $p\ge 63$, and assume $\frac{23}{50}p < C(p)$ and $E(p,\frac{91}{250}) < C(p)$. If the Hlawka deficit of three real vectors at height $C(p)$ is negative, there is a $3\times 3$ real matrix $X=(X_{ji})$ with negative triple deficit whose entries obey
--   $$
--   -\frac{273}{250}\le X_{jj}\le -\frac{7813}{10500},\qquad
--   \frac{7813}{10500}\le X_{ji}\le \frac{273}{250}\ (i\ne j).
--   $$
--
--   The lower entry $\frac{7813}{10500}$ is the frozen left endpoint of the cutoff-$63$ confinement at radius $\frac{91}{250}$.
--
--   **Formalization Note.** The box is the set comprehension in `local_failure63`; `Triple` is `Fin 3 \to Fin 3 \to \mathbb{R}`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — localization of a negative cyclic deficit into the cutoff-63 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.local_failure63 : ∀ p : ℝ, 63 ≤ p →
    (23 / 50 : ℝ) * p < cyclicConstant p →
    scalarEnvelope p (91 / 250) < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ ({X : Triple | ∀ j i,
          if j = i then -(273 / 250 : ℝ) ≤ X j i ∧ X j i ≤ -(7813 / 10500 : ℝ)
          else (7813 / 10500 : ℝ) ≤ X j i ∧ X j i ≤ (273 / 250 : ℝ)} : Set Triple),
          tripleDeficit p (cyclicConstant p) X < 0 := by sorry
