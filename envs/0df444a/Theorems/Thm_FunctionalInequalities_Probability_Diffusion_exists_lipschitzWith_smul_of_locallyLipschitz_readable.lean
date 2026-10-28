-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_exists_lipschitzWith_smul_of_locallyLipschitz_readable
-- name    : FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:22.213706+00:00
-- url     : https://prove2.me/theorems/a69c5efc-cc10-4d88-8cc4-a8588fa667cb
-- title:
--   Global Lipschitzness of a Compactly Supported Cutoff Product
-- statement:
--   This is the cutoff localization statement labeled S5d.
--
--   Let $V$ be a finite-dimensional real normed space, $V'$ a real normed space, and let $\gamma:V\to\mathbb R$ be Lipschitz with a nonnegative Lipschitz constant and compact support. Let $f:V\to V'$ be locally Lipschitz. Then there exist $K\in\mathbb R_{\ge0}$ and $B\in\mathbb R$ such that:
--
--   1. the map $x\mapsto\gamma(x)\,f(x)$ is globally Lipschitz with constant $K$;
--   2. for every $x\in V$,
--   $$\|\gamma(x)f(x)\|\le B.$$
--
--   Scalar multiplication is the given action of $\mathbb R$ on $V'$. The theorem is a compact-localization tool and does not assert a particular formula for either bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_lipschitzWith_smul_of_locallyLipschitz {γ : V → ℝ} {Kγ : ℝ≥0}
--       (hγ : LipschitzWith Kγ γ) (hγs : HasCompactSupport γ) {f : V → V'}
--       (hf : LocallyLipschitz f) :
--       (∃ K : ℝ≥0, LipschitzWith K fun x => γ x • f x) ∧ ∃ B : ℝ, ∀ x, ‖γ x • f x‖ ≤ B
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Cutoff/LipschitzBall`](https://prove2.me/theorems/ff179ecc-cd31-4939-9396-b1ea0665ce64).
--
--   [Source excerpt, lines 55–58](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/LipschitzBall.lean#L55-L58) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/LipschitzBall.lean#L53-L133 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.LipschitzBall`, declaration `FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall

open scoped NNReal
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']

theorem FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz_readable {γ : V → ℝ} {Kγ : ℝ≥0}
    (hγ : LipschitzWith Kγ γ) (hγs : HasCompactSupport γ) {f : V → V'}
    (hf : LocallyLipschitz f) :
    (∃ K : ℝ≥0, LipschitzWith K fun x => γ x • f x) ∧ ∃ B : ℝ, ∀ x, ‖γ x • f x‖ ≤ B := by sorry
