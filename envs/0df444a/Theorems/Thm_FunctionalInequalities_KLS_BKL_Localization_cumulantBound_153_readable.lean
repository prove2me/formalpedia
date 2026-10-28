-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cumulantBound_153_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.cumulantBound_153_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:22:28.356575+00:00
-- url     : https://prove2.me/theorems/ea132ff5-d4da-4638-93df-e2e8e356623d
-- title:
--   Closed Cumulant Bound with Constant $153$
-- statement:
--   For every $d\ge 1$, every dimension $m$, every isotropic log-concave probability law $\nu$ on $\mathbb R^m$ and every vector $u$, the $(d+1)$-st cumulant tensor satisfies
--
--   $$
--   \sum_J \kappa_{d+1}(u,e_{J_1},\dots,e_{J_d})^2\le (d!)^2\,153^{d}\,\|u\|^2,
--   $$
--
--   where $J$ ranges over all $d$-tuples of coordinate indices, i.e. $R^\nu_{d+1}\le 153^{d}(d!)^2\,\mathrm{Id}$. This is Theorem 4.1 of BKL with one explicit universal constant, obtained from the cutoff induction and the compact Letwin bound. Source: BKL arXiv:2610.05474v1, Theorem 4.1, p. 18.
--
--   **Original Lean source**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context.
--
--   ```lean
--   theorem cumulantBound_153 : ∀ d : ℕ, 1 ≤ d →
--       LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d) :=
--     cumulantBound_of_letwinCompact LogConcave.Suspension.letwinCompactBound
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantBound`](https://prove2.me/theorems/2a920c1d-59d7-44d6-9244-3f5151f5e420).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3).
--
--   Selected supporting theorems: [`cumulantBoundCompact_of_cutoffEnergyClaim`](https://prove2.me/theorems/a3ff251c-553e-44e1-9529-aa9e7643ca87), [`cutoffEnergyClaim_all`](https://prove2.me/theorems/8ed09f22-1ad1-4f50-a5e4-04b6280a1b1e), [`cutoffEnergyClaim_succ`](https://prove2.me/theorems/8ae5977b-ab49-4d46-8c59-295ce589f83a), [`generator_cumulantEnergy_ge`](https://prove2.me/theorems/d995a803-9dc2-4144-b611-6d14e68dd120), [`cumulantBound_of_compact`](https://prove2.me/theorems/642ea310-0dfa-47d8-b6bd-18048856ed8f).
--
--   Previous: [`cutoffEnergyClaim_153`](https://prove2.me/theorems/8321e3a6-398a-4003-8e41-2eaf4a0c8527).
--
--   [Source excerpt, lines 25–27](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantBound.lean#L25-L27) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantBound.lean#L23-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantBound`, declaration `FunctionalInequalities.KLS.BKL.Localization.cumulantBound_153`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantBound

theorem FunctionalInequalities.KLS.BKL.Localization.cumulantBound_153_readable : ∀ d : ℕ, 1 ≤ d →
    LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d) := by sorry
