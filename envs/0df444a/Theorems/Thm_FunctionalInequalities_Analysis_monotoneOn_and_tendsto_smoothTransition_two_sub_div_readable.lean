-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_monotoneOn_and_tendsto_smoothTransition_two_sub_div_readable
-- name    : FunctionalInequalities.Analysis.monotoneOn_and_tendsto_smoothTransition_two_sub_div_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:29.26368+00:00
-- url     : https://prove2.me/theorems/07c7bff6-a883-4a34-a1d3-2095c97849b8
-- title:
--   Monotone Smooth-Transition Exhaustion
-- statement:
--   This formalizes the scalar exhaustion part of Lemma A.4 of Letwin (arXiv:2607.24164v1), p. 17.
--
--   For every $a\in\mathbb R$, define
--   $$
--   \chi_R=\operatorname{smoothTransition}(2-a/R).
--   $$
--   As a function of the positive parameter $R$, $\chi_R$ is monotone on $(0,\infty)$, and
--   $$
--   \lim_{R\to\infty}\operatorname{smoothTransition}(2-a/R)=1.
--   $$
--   The limit is expressed as convergence along the real filter `atTop` to the neighborhood of $1$.
--
--   This is a scalar monotone-exhaustion tool for cutoff constructions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem monotoneOn_and_tendsto_smoothTransition_two_sub_div (a : ℝ) :
--       MonotoneOn (fun R : ℝ => Real.smoothTransition (2 - a / R)) (Set.Ioi 0) ∧
--         Filter.Tendsto (fun R : ℝ => Real.smoothTransition (2 - a / R)) Filter.atTop (nhds 1)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Cutoff/Profile`](https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219).
--
--   Previous: [`deriv_comp_sub_div_and_deriv_deriv`](https://prove2.me/theorems/41078cd2-f599-4095-aec6-d7ad2870689d).
--
--   [Source excerpt, lines 422–424](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L422-L424) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L420-L468 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.monotoneOn_and_tendsto_smoothTransition_two_sub_div`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile

theorem FunctionalInequalities.Analysis.monotoneOn_and_tendsto_smoothTransition_two_sub_div_readable (a : ℝ) :
    MonotoneOn (fun R : ℝ => Real.smoothTransition (2 - a / R)) (Set.Ioi 0) ∧
      Filter.Tendsto (fun R : ℝ => Real.smoothTransition (2 - a / R)) Filter.atTop (nhds 1) := by sorry
