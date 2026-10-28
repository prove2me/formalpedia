-- Prove2me | Theorems.Thm_GreedyRS_Greedy_lemma2_Cfun_strictAnti_continuous
-- name    : GreedyRS.Greedy.lemma2_Cfun_strictAnti_continuous
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T10:36:49.533403+00:00
-- url     : https://prove2.me/theorems/1a40acf8-48e9-4475-be92-93b39fc1fe3a
-- title:
--   Lemma 2 (analytic part), p. 14; proof EC.1.2 — C(x) = exp(Σ Φ(−√n x)/n) is continuous and strictly decreasing on (0, ∞)
-- statement:
--   Let $\Phi$ be the standard normal distribution function and, for $x > 0$,
--   $$C(x) = \exp\Big(\sum_{n=1}^{\infty} \frac{1}{n}\,\Phi\big(-\sqrt{n}\,x\big)\Big).$$
--   Then $C$ is **continuous and strictly decreasing on $(0,\infty)$**.
--
--   This is the analytic part of Lemma 2 of the source. There it is stated for $\mathbb E[\tilde N(x)]$, which by (4.1) equals $C(x)$. It is what lets one choose levels $\gamma_0$ and $\gamma_\epsilon^\pm$ with $C((\gamma-\gamma_0)/\sigma)=c$ and $C((\gamma-\gamma_\epsilon^\pm)/\sigma)=c\mp2\epsilon$, and have $\gamma_\epsilon^\pm\to\gamma_0$, in the proofs of Theorems 1 and 2.
--
--   **Formalization Note.** $C$ is the platform definition `GreedyRS.Greedy.Cfun`, with the series indexed from $n+1$, $n \ge 0$. $\Phi$ is `GreedyRS.Greedy.Phi`, the cdf of `gaussianReal 0 1`. The two claims are `StrictAntiOn` and `ContinuousOn` on `Set.Ioi 0`.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 14, Lemma 2 (continuity and strict monotonicity of C on (0,∞)); proof EC.1.2, pp. ec1–ec2

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
open MeasureTheory ProbabilityTheory

namespace GreedyRS.Greedy

theorem lemma2_Cfun_strictAnti_continuous :
    StrictAntiOn Cfun (Set.Ioi 0) ∧ ContinuousOn Cfun (Set.Ioi 0) := by sorry

end GreedyRS.Greedy
