-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_majorant_abs_deriv_deriv_smoothTransition_two_sub_readable
-- name    : FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:21.135323+00:00
-- url     : https://prove2.me/theorems/75594fe5-03f9-45fd-97be-284edaa2d948
-- title:
--   Smooth Compact Majorant for the Cutoff Curvature
-- statement:
--   This formalizes a scalar component of Lemma A.4 of Letwin (arXiv:2607.24164v1).
--
--   For $\eta(t)=\operatorname{smoothTransition}(2-t)$, there exists a smooth compactly supported function $w:\mathbb R\to\mathbb R$ such that $w\ge0$, $w(t)=0$ whenever $t\le0$ or $3\le t$, and
--
--   $$|\eta''(t)|\le w(t)\qquad(t\in\mathbb R).$$
--
--   The function $w$ is a technical compact majorant for the second derivative of the scalar cutoff.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_majorant_abs_deriv_deriv_smoothTransition_two_sub :
--       ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧ (∀ t, 0 ≤ w t) ∧
--         (∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) ∧
--         ∀ t, |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ w t
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Cutoff/Profile`](https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219).
--
--   Supporting theorems: [`smoothTransition_two_sub_cutoff`](https://prove2.me/theorems/107a6021-a617-4338-a167-9789f56e48be).
--
--   Previous: [`smoothTransition_two_sub_cutoff`](https://prove2.me/theorems/107a6021-a617-4338-a167-9789f56e48be) · Next: [`inv_mul_intervalIntegral_div_three_cutoff`](https://prove2.me/theorems/84c111d5-1c7e-41d4-975d-61430e96ccc6).
--
--   [Source excerpt, lines 126–129](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L126-L129) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L124-L192 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile

open scoped ContDiff

theorem FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub_readable :
    ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧ (∀ t, 0 ≤ w t) ∧
      (∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) ∧
      ∀ t, |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ w t := by sorry
