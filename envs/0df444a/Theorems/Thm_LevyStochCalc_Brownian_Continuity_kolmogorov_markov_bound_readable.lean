-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kolmogorov_markov_bound_readable
-- name    : LevyStochCalc.Brownian.Continuity.kolmogorov_markov_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:33.778839+00:00
-- url     : https://prove2.me/theorems/cc3bbae1-93c7-4b2a-a726-18938f9d796c
-- title:
--   Kolmogorov Process Increment Tail Bound
-- statement:
--   This statement gives the Markov–Chebyshev tail estimate associated with a Kolmogorov process.
--
--   Let $\Omega$ be a measurable space, let $P$ be a probability measure on $\Omega$, and let $X : \mathbb{R} \to \Omega \to \mathbb{R}$ be a real-valued process. Let $p,q \in \mathbb{R}$ and $M \in [0,\infty)$, and assume the process satisfies `ProbabilityTheory.IsKolmogorovProcess X P p q M`. For arbitrary times $s,t \in \mathbb{R}$, let $\lambda \in [0,\infty]$ satisfy:
--
--   1. $0 < \lambda$;
--   2. $\lambda \ne \infty$.
--
--   Writing `edist` for the extended distance, the probability of an increment exceeding the threshold $\lambda$ is bounded by
--
--   $$
--   P\bigl(\{\omega \mid \lambda \le \operatorname{edist}(X(s,\omega),X(t,\omega))\}\bigr)
--   \le
--   \frac{M\,\operatorname{edist}(s,t)^q}{\lambda^p}.
--   $$
--
--   Here the right-hand side is interpreted in $[0,\infty]$, with $M$ coerced from $[0,\infty)$ to `ENNReal`; the powers are extended-real powers. This is a per-pair increment tail estimate that can be reused in convergence-in-measure and summability arguments for continuous modifications of stochastic processes.
--
--   **Formalization Note** The measure-valued quantity and all arithmetic in the conclusion use `ENNReal`; the hypotheses require the threshold to be strictly positive and not equal to `⊤`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma kolmogorov_markov_bound
--       (P : Measure Ω) [IsProbabilityMeasure P]
--       (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
--       (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
--       (s t : ℝ) {lam : ℝ≥0∞} (hlam_pos : 0 < lam) (hlam_top : lam ≠ ⊤) :
--       P {ω | lam ≤ edist (X s ω) (X t ω)}
--         ≤ (M : ℝ≥0∞) * edist s t ^ q / lam ^ p
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityKolmogorovBounds`](https://prove2.me/theorems/db501a14-f954-4e21-a7e6-2ee411f6aff8).
--
--   Next: [`kc_level_bad_measure`](https://prove2.me/theorems/0aab2f8f-d712-4737-86f0-b7eebb793739).
--
--   [Source excerpt, lines 42–48](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L42-L48) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L31-L75 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kolmogorov_markov_bound`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Continuity.kolmogorov_markov_bound_readable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ≥0∞} (hlam_pos : 0 < lam) (hlam_top : lam ≠ ⊤) :
    P {ω | lam ≤ edist (X s ω) (X t ω)}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / lam ^ p := by sorry
