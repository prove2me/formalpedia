-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_local_failure70
-- name    : HlawkaSchatten.DiagonalCutoff.local_failure70
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T04:14:56.829164+00:00
-- url     : https://prove2.me/theorems/8ca5e1de-d212-44d2-a91f-c522141166aa
-- title:
--   A negative deficit localizes into the cutoff-70 entry box
-- statement:
--   If the cyclic constant exceeds both $\frac{23}{50}p$ and the scalar envelope at $\frac{73}{200}$, then any real three-coordinate counterexample to the cyclic bound can be rotated and signed into a fixed asymmetric box on which the triple deficit is still negative.
--
--   Let $p\ge 70$, and assume $\frac{23}{50}p < C(p)$ and $E(p,\frac{73}{200}) < C(p)$. Write $D_p(x,y,z)$ for the Hlawka deficit of three real vectors at height $C(p)$. If $D_p(x,y,z)<0$, there is a $3\times 3$ real matrix $X=(X_{ji})$ such that the associated triple deficit is negative and the entries obey
--
--   $$
--   -\frac{219}{200}\le X_{jj}\le -\frac{5217}{7000},\qquad
--   \frac{5217}{7000}\le X_{ji}\le \frac{219}{200}\ (i\ne j).
--   $$
--
--   The diagonal is the negative coordinate and the off-diagonal entries are the positive ones. This is the localization step of the cutoff-$70$ argument: every counterexample meets this box.
--
--   **Formalization Note.** The box is the set comprehension in `local_failure70`; `Triple` is `Fin 3 → Fin 3 → ℝ`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — localization of a negative cyclic deficit into the cutoff-70 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.local_failure70 : ∀ p : ℝ, 70 ≤ p →
    (23 / 50 : ℝ) * p < cyclicConstant p →
    scalarEnvelope p (73 / 200) < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ ({X : Triple | ∀ j i,
          if j = i then -(219 / 200 : ℝ) ≤ X j i ∧ X j i ≤ -(5217 / 7000 : ℝ)
          else (5217 / 7000 : ℝ) ≤ X j i ∧ X j i ≤ (219 / 200 : ℝ)} : Set Triple),
          tripleDeficit p (cyclicConstant p) X < 0 := by sorry
