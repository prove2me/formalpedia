-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_local_failure65
-- name    : HlawkaSchatten.DiagonalCutoff.local_failure65
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T06:02:15.351981+00:00
-- url     : https://prove2.me/theorems/3dcf7e9a-59c9-4932-88e0-90797dae7276
-- title:
--   A negative deficit localizes into the cutoff-65 entry box
-- statement:
--   If the cyclic constant exceeds both $\frac{23}{50}p$ and the scalar envelope at $\frac{91}{250}$, then any real three-coordinate counterexample to the cyclic bound can be rotated and signed into a fixed asymmetric box on which the triple deficit is still negative.
--
--   Let $p\ge 65$, and assume $\frac{23}{50}p < C(p)$ and $E(p,\frac{91}{250}) < C(p)$. Write $D_p(x,y,z)$ for the Hlawka deficit of three real vectors at height $C(p)$. If $D_p(x,y,z)<0$, there is a $3\times 3$ real matrix $X=(X_{ji})$ such that the associated triple deficit is negative and the entries obey
--
--   $$
--   -\frac{273}{250}\le X_{jj}\le -\frac{4851}{6500},\qquad
--   \frac{4851}{6500}\le X_{ji}\le \frac{273}{250}\ (i\ne j).
--   $$
--
--   The diagonal is the negative coordinate and the off-diagonal entries are the positive ones. The lower entry $\frac{4851}{6500}$ is the frozen left-endpoint value of the cutoff-$65$ confinement.
--
--   **Formalization Note.** The box is the set comprehension in `local_failure65`; `Triple` is `Fin 3 \to Fin 3 \to \mathbb{R}`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — localization of a negative cyclic deficit into the cutoff-65 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.local_failure65 : ∀ p : ℝ, 65 ≤ p →
    (23 / 50 : ℝ) * p < cyclicConstant p →
    scalarEnvelope p (91 / 250) < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ ({X : Triple | ∀ j i,
          if j = i then -(273 / 250 : ℝ) ≤ X j i ∧ X j i ≤ -(4851 / 6500 : ℝ)
          else (4851 / 6500 : ℝ) ≤ X j i ∧ X j i ≤ (273 / 250 : ℝ)} : Set Triple),
          tripleDeficit p (cyclicConstant p) X < 0 := by sorry
