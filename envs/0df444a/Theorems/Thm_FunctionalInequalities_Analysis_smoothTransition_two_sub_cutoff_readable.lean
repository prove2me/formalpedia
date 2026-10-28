-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_smoothTransition_two_sub_cutoff_readable
-- name    : FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:27.51467+00:00
-- url     : https://prove2.me/theorems/107a6021-a617-4338-a167-9789f56e48be
-- title:
--   Smooth Two-Scale Cutoff Profile
-- statement:
--   This formalizes the scalar part of Lemma A.4 of Letwin (arXiv:2607.24164v1), with a stronger standalone profile statement.
--
--   Define $\eta(t)=\operatorname{smoothTransition}(2-t)$. Then $\eta$ is smooth and antitone, satisfies $0\le\eta(t)\le1$, equals $1$ for $t\le1$, and equals $0$ for $t\ge2$. If $t<1$ or $t>2$, then $\eta'(t)=\eta''(t)=0$. Both $\eta'$ and $\eta''$ have compact support, and there exists $B\ge0$ such that
--
--   $$|\eta'(t)|\le B\quad\text{and}\quad|\eta''(t)|\le B\qquad(t\in\mathbb R).$$
--
--   This is reusable scalar cutoff infrastructure; it does not construct the paper’s full generator estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem smoothTransition_two_sub_cutoff :
--       ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 - s)) ∧ Antitone (fun s : ℝ => Real.smoothTransition (2 - s)) ∧
--         (∀ t : ℝ, 0 ≤ Real.smoothTransition (2 - t) ∧ Real.smoothTransition (2 - t) ≤ 1) ∧
--         (∀ t : ℝ, t ≤ 1 → Real.smoothTransition (2 - t) = 1) ∧
--         (∀ t : ℝ, 2 ≤ t → Real.smoothTransition (2 - t) = 0) ∧
--         (∀ t : ℝ, t < 1 ∨ 2 < t →
--           deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t = 0 ∧ deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t = 0) ∧
--         HasCompactSupport (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) ∧
--         HasCompactSupport (deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s)))) ∧
--         ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
--           |deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t| ≤ B ∧ |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ B
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Cutoff/Profile`](https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219).
--
--   Next: [`exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`](https://prove2.me/theorems/75594fe5-03f9-45fd-97be-284edaa2d948).
--
--   [Source excerpt, lines 35–45](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L35-L45) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L32-L122 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile

open scoped ContDiff

theorem FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff_readable :
    ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 - s)) ∧ Antitone (fun s : ℝ => Real.smoothTransition (2 - s)) ∧
      (∀ t : ℝ, 0 ≤ Real.smoothTransition (2 - t) ∧ Real.smoothTransition (2 - t) ≤ 1) ∧
      (∀ t : ℝ, t ≤ 1 → Real.smoothTransition (2 - t) = 1) ∧
      (∀ t : ℝ, 2 ≤ t → Real.smoothTransition (2 - t) = 0) ∧
      (∀ t : ℝ, t < 1 ∨ 2 < t →
        deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t = 0 ∧ deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t = 0) ∧
      HasCompactSupport (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) ∧
      HasCompactSupport (deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s)))) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
        |deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t| ≤ B ∧ |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ B := by sorry
