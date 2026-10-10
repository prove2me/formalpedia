-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_local_failure64
-- name    : HlawkaSchatten.DiagonalCutoff.local_failure64
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T06:50:29.28898+00:00
-- url     : https://prove2.me/theorems/e4e35ff2-1286-42e9-b573-fe5c621b31ea
-- title:
--   A negative deficit localizes into the cutoff-64 entry box
-- statement:
--   If the cyclic constant exceeds both $\frac{23}{50}p$ and the scalar envelope at $\frac{91}{250}$, then any real three-coordinate counterexample to the cyclic bound can be rotated and signed into a fixed asymmetric box on which the triple deficit is still negative.
--
--   Let $p\ge 64$, and assume $\frac{23}{50}p < C(p)$ and $E(p,\frac{91}{250}) < C(p)$. Write $D_p(x,y,z)$ for the Hlawka deficit of three real vectors at height $C(p)$. If $D_p(x,y,z)<0$, there is a $3\times 3$ real matrix $X=(X_{ji})$ such that the associated triple deficit is negative and the entries obey
--
--   $$
--   -\frac{273}{250}\le X_{jj}\le -\frac{23847}{32000},\qquad
--   \frac{23847}{32000}\le X_{ji}\le \frac{273}{250}\ (i\ne j).
--   $$
--
--   The diagonal is the negative coordinate and the off-diagonal entries are the positive ones. The lower entry $\frac{23847}{32000}$ is the frozen left-endpoint value of the cutoff-$64$ confinement at the same radius $\frac{91}{250}$.
--
--   **Formalization Note.** The box is the set comprehension in `local_failure64`; `Triple` is `Fin 3 \to Fin 3 \to \mathbb{R}`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — localization of a negative cyclic deficit into the cutoff-64 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.local_failure64 : ∀ p : ℝ, 64 ≤ p →
    (23 / 50 : ℝ) * p < cyclicConstant p →
    scalarEnvelope p (91 / 250) < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ ({X : Triple | ∀ j i,
          if j = i then -(273 / 250 : ℝ) ≤ X j i ∧ X j i ≤ -(23847 / 32000 : ℝ)
          else (23847 / 32000 : ℝ) ≤ X j i ∧ X j i ≤ (273 / 250 : ℝ)} : Set Triple),
          tripleDeficit p (cyclicConstant p) X < 0 := by sorry
