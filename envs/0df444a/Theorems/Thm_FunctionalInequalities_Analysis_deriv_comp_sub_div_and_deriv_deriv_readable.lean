-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_deriv_comp_sub_div_and_deriv_deriv_readable
-- name    : FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:53.496475+00:00
-- url     : https://prove2.me/theorems/41078cd2-f599-4095-aec6-d7ad2870689d
-- title:
--   Affine Rescaling Of First And Second Derivatives
-- statement:
--   This formalizes the affine rescaling identities cited from Letwin (arXiv:2607.24164v1), locator Lemma A.4, with the reviewed relation recorded as stronger.
--
--   Let $f:\mathbb R\to\mathbb R$ and let $c,R,t\in\mathbb R$. Define $g(s)=f((s-c)/R)$. Then, using Lean's total derivative convention,
--   $$g'(t)=R^{-1}f'\!\left(\frac{t-c}{R}\right),$$
--   and
--   $$g''(t)=(R^{-1})^2f''\!\left(\frac{t-c}{R}\right).$$
--
--   No differentiability assumptions and no condition $R\ne0$ are required in the formal statement.
--
--   This is a generic scalar calculus identity used in rescaling cutoff profiles.
--
--   **Formalization Note** The derivatives are Lean's total `deriv` operators, so the statement includes degenerate cases such as $R=0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem deriv_comp_sub_div_and_deriv_deriv (f : ℝ → ℝ) (c R t : ℝ) :
--       deriv (fun s => f ((s - c) / R)) t = R⁻¹ * deriv f ((t - c) / R) ∧
--         deriv (deriv (fun s => f ((s - c) / R))) t = (R⁻¹) ^ 2 * deriv (deriv f) ((t - c) / R)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Cutoff/Profile`](https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219).
--
--   Previous: [`inv_mul_intervalIntegral_div_three_cutoff`](https://prove2.me/theorems/84c111d5-1c7e-41d4-975d-61430e96ccc6) · Next: [`monotoneOn_and_tendsto_smoothTransition_two_sub_div`](https://prove2.me/theorems/07c7bff6-a883-4a34-a1d3-2095c97849b8).
--
--   [Source excerpt, lines 383–385](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L383-L385) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L380-L417 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile

theorem FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv_readable (f : ℝ → ℝ) (c R t : ℝ) :
    deriv (fun s => f ((s - c) / R)) t = R⁻¹ * deriv f ((t - c) / R) ∧
      deriv (deriv (fun s => f ((s - c) / R))) t = (R⁻¹) ^ 2 * deriv (deriv f) ((t - c) / R) := by sorry
