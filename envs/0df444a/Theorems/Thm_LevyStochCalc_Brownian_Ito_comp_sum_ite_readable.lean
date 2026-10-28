-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_comp_sum_ite_readable
-- name    : LevyStochCalc.Brownian.Ito.comp_sum_ite_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:10.215065+00:00
-- url     : https://prove2.me/theorems/d50428dd-fbc4-4845-8772-c63abee73b25
-- title:
--   Composition of a Step Sum with a Zero-Preserving Function
-- statement:
--   This finite-sum lemma states that a function fixing zero commutes with the step sum associated with a strictly increasing partition.
--
--   Let $\pi:\operatorname{Fin}(M+1)\to\mathbb R$ be strictly monotone, let $f:\operatorname{Fin}(M)\to\mathbb R$, let $s\in\mathbb R$, and let $g:\mathbb R\to\mathbb R$ satisfy $g(0)=0$. Then
--
--   $$
--   g\!\left(\sum_{j=0}^{M-1}\mathbf 1_{(\pi_j,\pi_{j+1}]}(s)f_j\right)
--   =\sum_{j=0}^{M-1}\mathbf 1_{(\pi_j,\pi_{j+1}]}(s)g(f_j).
--   $$
--
--   Because the partition is strictly increasing, at most one step is active. The lemma is useful for passing powers and other zero-preserving operations through elementary-integrand evaluations.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem comp_sum_ite {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
--       (f : Fin M → ℝ) (s : ℝ) (g : ℝ → ℝ) (hg0 : g 0 = 0) :
--       g (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
--         = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g (f j) else 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentLintegral`](https://prove2.me/theorems/e9dd3a38-7a56-4504-970d-056a933b183f).
--
--   Next: [`abs_clamp_sub_le`](https://prove2.me/theorems/1920857f-1d3d-455c-88bd-4b390cbdc408).
--
--   [Source excerpt, lines 27–30](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean#L27-L30) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean#L26-L55 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentLintegral`, declaration `LevyStochCalc.Brownian.Ito.comp_sum_ite`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u

theorem LevyStochCalc.Brownian.Ito.comp_sum_ite_readable {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    (f : Fin M → ℝ) (s : ℝ) (g : ℝ → ℝ) (hg0 : g 0 = 0) :
    g (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
      = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g (f j) else 0 := by sorry
