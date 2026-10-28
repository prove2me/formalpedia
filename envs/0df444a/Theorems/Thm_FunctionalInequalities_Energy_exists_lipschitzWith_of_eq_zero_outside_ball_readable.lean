-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_exists_lipschitzWith_of_eq_zero_outside_ball_readable
-- name    : FunctionalInequalities.Energy.exists_lipschitzWith_of_eq_zero_outside_ball_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:52.922901+00:00
-- url     : https://prove2.me/theorems/edf2acd8-cdce-45dd-bafd-8681d2aeaf30
-- title:
--   Global Lipschitzness of Locally Lipschitz Compactly Supported Functions
-- statement:
--   This statement is the bounded-support Lipschitz principle.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $g:V\to\mathbb R$ be locally Lipschitz, and let $R\in\mathbb R$. Assume that $g$ vanishes outside the closed ball of radius $R$ centered at the origin, in the sense that
--
--   $$
--   R\leq\|x\|\quad\Longrightarrow\quad g(x)=0
--   $$
--
--   for every $x\in V$.
--
--   Then there exists some $K\in[0,\infty)$ such that $g$ is globally $K$-Lipschitz:
--
--   $$
--   \exists K\in[0,\infty),\qquad \operatorname{LipschitzWith}(K,g).
--   $$
--
--   The conclusion is existential and does not specify a particular Lipschitz constant. It supplies a standard reduction from locally Lipschitz functions with bounded support to globally Lipschitz tests.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_lipschitzWith_of_eq_zero_outside_ball {g : V → ℝ} {R : ℝ}
--       (hg : LocallyLipschitz g) (hR : ∀ x, R ≤ ‖x‖ → g x = 0) :
--       ∃ K : ℝ≥0, LipschitzWith K g
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Recovery`](https://prove2.me/theorems/4d5469da-893c-48b4-9cb5-3ecfda5a30ce).
--
--   Previous: [`locallyLipschitz_mul`](https://prove2.me/theorems/0d72763a-6b0b-466f-9759-3b5ebd4e877f) · Next: [`apply_mul_le`](https://prove2.me/theorems/bf9de844-4401-433d-8497-f00f6238df47).
--
--   [Source excerpt, lines 251–253](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L251-L253) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L250-L300 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, declaration `FunctionalInequalities.Energy.exists_lipschitzWith_of_eq_zero_outside_ball`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery

open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Energy.exists_lipschitzWith_of_eq_zero_outside_ball_readable {g : V → ℝ} {R : ℝ}
    (hg : LocallyLipschitz g) (hR : ∀ x, R ≤ ‖x‖ → g x = 0) :
    ∃ K : ℝ≥0, LipschitzWith K g := by sorry
