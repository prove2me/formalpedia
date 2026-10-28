-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_mul_le_readable
-- name    : FunctionalInequalities.Energy.LocalSlope.apply_mul_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:53.495121+00:00
-- url     : https://prove2.me/theorems/bf9de844-4401-433d-8497-f00f6238df47
-- title:
--   Local-Slope Product Bound With A Bounded Lipschitz Factor
-- statement:
--   This is a one-moving-point product estimate for the local slope.
--
--   Let $V$ be a normed additive group, let $g,h:V\to\mathbb R$, and let $N\in[0,\infty)$ be represented by `NNReal`. Assume that $h$ is globally $N$-Lipschitz and bounded in absolute value by one:
--
--   $$
--   \operatorname{LipschitzWith}(N,h),
--   \qquad |h(y)|\le 1\quad\text{for every }y\in V.
--   $$
--
--   Then for every $x\in V$,
--
--   $$
--   \operatorname{apply}(y\mapsto g(y)h(y),x)
--   \le
--   \operatorname{apply}(g,x)+\operatorname{ENNReal.ofReal}(|g(x)|)\,N.
--   $$
--
--   The declaration is `apply_mul_le_readable`. The target values are in $[0,\infty]$; no inner-product, completeness, or finite-dimensionality assumptions are part of the statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.LocalSlope`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem apply_mul_le (g h : V → ℝ) {N : ℝ≥0} (hh : LipschitzWith N h)
--       (hh1 : ∀ y, |h y| ≤ 1) (x : V) :
--       apply (fun y ↦ g y * h y) x ≤ apply g x + ENNReal.ofReal |g x| * N
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Recovery`](https://prove2.me/theorems/4d5469da-893c-48b4-9cb5-3ecfda5a30ce).
--
--   Definition modules: [`Energy/LocalSlope/Basic`](https://prove2.me/theorems/403376af-90fc-4aef-aed0-aefc10593586).
--
--   Previous: [`exists_lipschitzWith_of_eq_zero_outside_ball`](https://prove2.me/theorems/edf2acd8-cdce-45dd-bafd-8681d2aeaf30) · Next: [`lipschitzOnWith_mollify_ball`](https://prove2.me/theorems/f6c8681b-1ff6-4044-8f83-791d558075e3).
--
--   [Source excerpt, lines 403–405](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L403-L405) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L400-L446 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, declaration `FunctionalInequalities.Energy.LocalSlope.apply_mul_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery

open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
omit [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Energy.LocalSlope.apply_mul_le_readable (g h : V → ℝ) {N : ℝ≥0} (hh : LipschitzWith N h)
    (hh1 : ∀ y, |h y| ≤ 1) (x : V) :
    apply (fun y ↦ g y * h y) x ≤ apply g x + ENNReal.ofReal |g x| * N := by sorry
