-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_copies_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.exists_copies_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:00.096529+00:00
-- url     : https://prove2.me/theorems/5967f3b2-764f-4fd4-8e97-8cae228211c5
-- title:
--   Existence Of A Suitable Number Of Copies
-- statement:
--   This statement formalizes the numerical choice of the number of copies in the suspension construction.
--
--   Let $a,\beta,M\in\mathbb R$ satisfy
--   $$a>0,\qquad \beta\ge0,\qquad M\ge0.$$
--   Then there exists an integer $N>0$ such that
--   $$\frac{\beta}{\sqrt N}M\le a.$$
--
--   The result guarantees a positive finite copy number for any positive curvature parameter and finite nonnegative Hessian bound. It is the numerical existence component of the suspension convexity condition.
--
--   **Formalization Note.** The square root uses the real coercion of $N$; the conclusion does not specify a particular choice of $N$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_copies {a beta M : ℝ} (ha : 0 < a) (hbeta : 0 ≤ beta) (hM : 0 ≤ M) :
--       ∃ N : ℕ, 0 < N ∧ beta / Real.sqrt N * M ≤ a
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Basic`](https://prove2.me/theorems/aaa7527c-3ccd-45dd-876d-0915bc183526).
--
--   Previous: [`convexOn_potential`](https://prove2.me/theorems/8bd14eff-e39b-41f3-a887-8c1cbe3d5c1e).
--
--   [Source excerpt, lines 108–109](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Basic.lean#L108-L109) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Basic.lean#L106-L123 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Basic`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.exists_copies`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Basic

theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_copies_readable {a beta M : ℝ} (ha : 0 < a) (hbeta : 0 ≤ beta) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ beta / Real.sqrt N * M ≤ a := by sorry
