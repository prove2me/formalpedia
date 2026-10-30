-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_eq_19_cosh_bound
-- name    : LightningNetwork.RateBounds.eq_19_cosh_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:50:59.425551+00:00
-- url     : https://prove2.me/theorems/f9ef28dd-5a92-4fc6-8f00-12e41a0e764d
-- title:
--   Eq. (19): $2(\cosh(C-\alpha)-1) \le e^{|C-\alpha|} - 1$
-- statement:
--   1. For every real $x$, $\cosh x = (e^x + e^{-x})/2 \le (e^{|x|} + 1)/2$.
--   2. Consequently, for all real $C$ and $\alpha$,
--   $$
--   2\bigl(\cosh(C-\alpha) - 1\bigr) \;\le\; e^{|C-\alpha|} - 1 .
--   $$
--
--   This replaces the hyperbolic condition in (18) by an exponential one.
--
--   Differences from the source:
--   - generalization: C > 0 (the cost of an on-chain transaction) and 0 < α < 1 → C and α any real numbers; reason: (19) is the instance x = C − α of the bound on cosh x, which the page states for every real x; the statement specializes to the page's C and α
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (19), p. 11

import Mathlib

namespace LightningNetwork.RateBounds

/-- **Inequality (19).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (19), p. 11: "Recall now that
cosh(x) = (e^x + e^{−x})/2 ≤ (e^{|x|} + 1)/2, whence 2(cosh(C − α) − 1) ≤ e^{|C−α|} − 1."

1. `cosh x ≤ (e^{|x|} + 1)/2` for every real `x`;
2. `2(cosh(C − α) − 1) ≤ e^{|C − α|} − 1` for all real `C`, `α`. -/
theorem eq_19_cosh_bound :
    (∀ x : ℝ, Real.cosh x ≤ (Real.exp |x| + 1) / 2) ∧
      ∀ C α : ℝ, 2 * (Real.cosh (C - α) - 1) ≤ Real.exp |C - α| - 1 := by sorry

end LightningNetwork.RateBounds
