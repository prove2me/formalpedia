-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_le_exp_mul_of_hasDerivAt_le_readable
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.le_exp_mul_of_hasDerivAt_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:08.898109+00:00
-- url     : https://prove2.me/theorems/38febeed-57be-4f77-b86b-1ca1d79ba62c
-- title:
--   Grönwall Bound on the Nonnegative Half-Line
-- statement:
--   This is a one-dimensional Grönwall inequality on $[0,\infty)$.
--
--   Let $E,E':\mathbb R\to\mathbb R$ and $c\in\mathbb R$. Assume:
--   1. $E$ is continuous on $[0,\infty)$.
--   2. For every $s>0$, $E$ has derivative $E'(s)$ at $s$.
--   3. For every $s>0$, $E'(s)\le cE(s)$.
--
--   Then, for every $t\ge0$,
--
--   $$
--   E(t)\le e^{ct}E(0).
--   $$
--
--   This result is a reusable differential-inequality lemma for exponential semigroup estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Semigroup.Generated`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem le_exp_mul_of_hasDerivAt_le {E E' : ℝ → ℝ} {c : ℝ} (hc : ContinuousOn E (Ici 0))
--       (hd : ∀ s, 0 < s → HasDerivAt E (E' s) s) (hle : ∀ s, 0 < s → E' s ≤ c * E s) {t : ℝ}
--       (ht : 0 ≤ t) :
--       E t ≤ Real.exp (c * t) * E 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Semigroup/Generated/Curvature`](https://prove2.me/theorems/2d0d4681-a28b-4386-bf7f-208cba5fd2c8).
--
--   Previous: [`hasDerivAt_inner_apply`](https://prove2.me/theorems/f5643287-fcd8-4cb8-adec-bac864e18749) · Next: [`norm_map_apply_sq_le_exp_of_mem_adjointComp`](https://prove2.me/theorems/3e1e0324-94fa-4fd6-b2c3-3d7551ff2d12).
--
--   [Source excerpt, lines 167–170](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L167-L170) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L165-L212 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Curvature`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.le_exp_mul_of_hasDerivAt_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature

open Filter Topology Set

theorem FunctionalInequalities.Analysis.Semigroup.Generated.le_exp_mul_of_hasDerivAt_le_readable {E E' : ℝ → ℝ} {c : ℝ} (hc : ContinuousOn E (Ici 0))
    (hd : ∀ s, 0 < s → HasDerivAt E (E' s) s) (hle : ∀ s, 0 < s → E' s ≤ c * E s) {t : ℝ}
    (ht : 0 ≤ t) :
    E t ≤ Real.exp (c * t) * E 0 := by sorry
