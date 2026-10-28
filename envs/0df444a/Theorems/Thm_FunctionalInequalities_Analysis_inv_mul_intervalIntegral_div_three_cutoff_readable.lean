-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inv_mul_intervalIntegral_div_three_cutoff_readable
-- name    : FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:44.213067+00:00
-- url     : https://prove2.me/theorems/84c111d5-1c7e-41d4-975d-61430e96ccc6
-- title:
--   Tail Primitive of a Compactly Supported Cutoff
-- statement:
--   Let $w:\mathbb R\to\mathbb R$ be smooth, nonnegative everywhere, and zero whenever $t\le0$ or $t\ge3$. Let $R>0$ and define
--   $$
--   q_R(t)=R^{-1}\int_{t/R}^{3}w(s)\,ds.
--   $$
--   Then $q_R$ is smooth,
--   $$
--   q_R'(t)=-R^{-2}w(t/R),
--   $$
--   $0\le q_R(t)$ for every $t$, and
--   $$
--   q_R(t)\le R^{-1}\int_0^3w(s)\,ds.
--   $$
--   Finally, $q_R(t)=0$ whenever $3R\le t$.
--
--   This scalar profile is a reusable cutoff component for noncompact integration by parts.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inv_mul_intervalIntegral_div_three_cutoff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
--       (hw0 : ∀ t, 0 ≤ w t) (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) :
--       ContDiff ℝ ∞ (fun t => R⁻¹ * ∫ s in t / R..3, w s) ∧
--         (∀ t, deriv (fun t => R⁻¹ * ∫ s in t / R..3, w s) t = -((R ^ 2)⁻¹ * w (t / R))) ∧
--         (∀ t, 0 ≤ R⁻¹ * ∫ s in t / R..3, w s) ∧
--         (∀ t, R⁻¹ * ∫ s in t / R..3, w s ≤ R⁻¹ * ∫ s in (0 : ℝ)..3, w s) ∧
--         (∀ t, 3 * R ≤ t → R⁻¹ * ∫ s in t / R..3, w s = 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Cutoff/Profile`](https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219).
--
--   Previous: [`exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`](https://prove2.me/theorems/75594fe5-03f9-45fd-97be-284edaa2d948) · Next: [`deriv_comp_sub_div_and_deriv_deriv`](https://prove2.me/theorems/41078cd2-f599-4095-aec6-d7ad2870689d).
--
--   [Source excerpt, lines 237–243](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L237-L243) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Lemma A.4 of Letwin (arXiv:2607.24164v1), p. 17, for its scalar tail primitive.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L234-L377 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile

open scoped ContDiff

theorem FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff_readable {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hw0 : ∀ t, 0 ≤ w t) (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun t => R⁻¹ * ∫ s in t / R..3, w s) ∧
      (∀ t, deriv (fun t => R⁻¹ * ∫ s in t / R..3, w s) t = -((R ^ 2)⁻¹ * w (t / R))) ∧
      (∀ t, 0 ≤ R⁻¹ * ∫ s in t / R..3, w s) ∧
      (∀ t, R⁻¹ * ∫ s in t / R..3, w s ≤ R⁻¹ * ∫ s in (0 : ℝ)..3, w s) ∧
      (∀ t, 3 * R ≤ t → R⁻¹ * ∫ s in t / R..3, w s = 0) := by sorry
