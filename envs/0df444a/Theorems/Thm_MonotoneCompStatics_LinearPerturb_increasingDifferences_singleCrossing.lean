-- Prove2me | Theorems.Thm_MonotoneCompStatics_LinearPerturb_increasingDifferences_singleCrossing
-- name    : MonotoneCompStatics.LinearPerturb.increasingDifferences_singleCrossing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:10.548986+00:00
-- url     : https://prove2.me/theorems/ee3fbfd3-9602-41a2-950c-a4909d1aa0be
-- title:
--   p. 164 remark — increasing differences in (x, t) imply the single crossing property
-- statement:
--   Let $X$ be a lattice, $T$ a partially ordered set and $f : X \times T \to \mathbb{R}$. Suppose $f$ has **increasing differences in $(x, t)$**: for $x' \ge x''$ in $X$, the difference $f(x', t) - f(x'', t)$ is monotone nondecreasing in $t$, that is,
--
--   $$
--   f(x', t') - f(x'', t') \ge f(x', t'') - f(x'', t'') \qquad \text{whenever } x' \ge x'' \text{ and } t' > t''.
--   $$
--
--   Then $f$ has the **single crossing property in $(x; t)$**: for $x' > x''$ and $t' > t''$, $f(x', t'') > f(x'', t'')$ implies $f(x', t') > f(x'', t')$, and $f(x', t'') \ge f(x'', t'')$ implies $f(x', t') \ge f(x'', t')$.
--
--   This is the second half of the remark following Theorem 5 in Milgrom and Shannon. It shows that the cardinal complementarity condition of Topkis is a special case of the ordinal one used in the Monotonicity Theorem.
--
--   **Formalization Note** Increasing differences is the published `Supermodularity.Monotonicity.IncreasingDifferencesOn f Set.univ`: for $t'' < t'$, the map $x \mapsto f(x, t') - f(x, t'')$ is monotone on $X$. This is the page's condition.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 164 (PDF p. 9), remark after Theorem 5

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing

namespace MonotoneCompStatics.LinearPerturb

/-- Milgrom and Shannon (1994), p. 164, remark after Theorem 5: a function `f : X × T → ℝ` on a
lattice `X` and a partially ordered set `T` with increasing differences in `(x, t)` has the single
crossing property in `(x; t)`. -/
theorem increasingDifferences_singleCrossing {X T : Type*} [Lattice X] [PartialOrder T]
    (f : X → T → ℝ)
    (hf : Supermodularity.Monotonicity.IncreasingDifferencesOn f Set.univ) :
    MonotoneCompStatics.Monotonicity.SingleCrossing f := by sorry

end MonotoneCompStatics.LinearPerturb
