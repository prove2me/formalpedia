-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_local_failure66
-- name    : HlawkaSchatten.DiagonalCutoff.local_failure66
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T05:17:48.935343+00:00
-- url     : https://prove2.me/theorems/100183aa-79df-460b-ac62-de7940eff2df
-- title:
--   A negative deficit localizes into the cutoff-66 entry box
-- statement:
--   If the cyclic constant exceeds both $\frac{23}{50}p$ and the scalar envelope at $\frac{73}{200}$, then any real three-coordinate counterexample to the cyclic bound can be rotated and signed into a fixed asymmetric box on which the triple deficit is still negative.
--
--   Let $p\ge 66$, and assume $\frac{23}{50}p < C(p)$ and $E(p,\frac{73}{200}) < C(p)$. Write $D_p(x,y,z)$ for the Hlawka deficit of three real vectors at height $C(p)$. If $D_p(x,y,z)<0$, there is a $3\times 3$ real matrix $X=(X_{ji})$ such that the associated triple deficit is negative and the entries obey
--
--   $$
--   -\frac{219}{200}\le X_{jj}\le -\frac{1631}{2200},\qquad
--   \frac{1631}{2200}\le X_{ji}\le \frac{219}{200}\ (i\ne j).
--   $$
--
--   The diagonal is the negative coordinate and the off-diagonal entries are the positive ones. This is the localization step of the cutoff-$66$ argument: every counterexample meets this box. The lower entry $\frac{1631}{2200}$ is the frozen left-endpoint value of the cutoff-$66$ confinement.
--
--   **Formalization Note.** The box is the set comprehension in `local_failure66`; `Triple` is `Fin 3 → Fin 3 → ℝ`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — localization of a negative cyclic deficit into the cutoff-66 asymmetric entry box.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.local_failure66 : ∀ p : ℝ, 66 ≤ p →
    (23 / 50 : ℝ) * p < cyclicConstant p →
    scalarEnvelope p (73 / 200) < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ ({X : Triple | ∀ j i,
          if j = i then -(219 / 200 : ℝ) ≤ X j i ∧ X j i ≤ -(1631 / 2200 : ℝ)
          else (1631 / 2200 : ℝ) ≤ X j i ∧ X j i ≤ (219 / 200 : ℝ)} : Set Triple),
          tripleDeficit p (cyclicConstant p) X < 0 := by sorry
