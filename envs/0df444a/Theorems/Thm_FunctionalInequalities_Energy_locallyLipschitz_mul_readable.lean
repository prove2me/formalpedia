-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_locallyLipschitz_mul_readable
-- name    : FunctionalInequalities.Energy.locallyLipschitz_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:06.508167+00:00
-- url     : https://prove2.me/theorems/0d72763a-6b0b-466f-9759-3b5ebd4e877f
-- title:
--   Local Lipschitz Product Rule with a Bounded Factor
-- statement:
--   This statement proves a local Lipschitz product rule.
--
--   Let $V$ be a normed additive commutative group, let $g,h:V\to\mathbb R$, and let $N\in[0,\infty)$. Assume:
--
--   1. $g$ is locally Lipschitz.
--   2. $h$ is globally $N$-Lipschitz.
--   3. $|h(x)|\leq 1$ for every $x\in V$.
--
--   Then the pointwise product is locally Lipschitz:
--
--   $$
--   x\mapsto g(x)h(x)\quad\text{is locally Lipschitz on }V.
--   $$
--
--   This is a technical reduction lemma for constructing locally Lipschitz cutoffs and products; no inner-product or finite-dimensional assumption is part of the statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem locallyLipschitz_mul {g h : V → ℝ} {N : ℝ≥0} (hg : LocallyLipschitz g)
--       (hh : LipschitzWith N h) (hh1 : ∀ x, |h x| ≤ 1) :
--       LocallyLipschitz (fun x ↦ g x * h x)
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Recovery`](https://prove2.me/theorems/4d5469da-893c-48b4-9cb5-3ecfda5a30ce).
--
--   Next: [`exists_lipschitzWith_of_eq_zero_outside_ball`](https://prove2.me/theorems/edf2acd8-cdce-45dd-bafd-8681d2aeaf30).
--
--   [Source excerpt, lines 201–203](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L201-L203) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L198-L246 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, declaration `FunctionalInequalities.Energy.locallyLipschitz_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery

open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
omit [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Energy.locallyLipschitz_mul_readable {g h : V → ℝ} {N : ℝ≥0} (hg : LocallyLipschitz g)
    (hh : LipschitzWith N h) (hh1 : ∀ x, |h x| ≤ 1) :
    LocallyLipschitz (fun x ↦ g x * h x) := by sorry
