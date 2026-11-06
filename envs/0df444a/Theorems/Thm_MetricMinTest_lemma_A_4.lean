-- Prove2me | Theorems.Thm_MetricMinTest_lemma_A_4
-- name    : MetricMinTest.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:38.358921+00:00
-- url     : https://prove2.me/theorems/664f30c6-8567-4054-9843-2c3990356c5f
-- title:
--   Lemma A.4, p.22 — signed Bernoulli bounds $\tfrac12(u-v)^2\le\mathrm{KL}(P_u\|P_v)\le2(u-v)^2$
-- statement:
--   Let $P_u$ denote the signed Bernoulli law of mean $u$. For means $u,v\in[-1/4,1/4]$,
--   $$\tfrac12(u-v)^2\le\mathrm{KL}(P_u\|P_v)\le\frac{(u-v)^2}{1-v^2}\le\tfrac{16}{15}(u-v)^2\le2(u-v)^2.$$
--
--   These bounds convert relative entropies between signed Bernoulli instances into squared mean differences; they drive the information lower bound (Theorem 3.1).
--
--   **Formalization Note** The relative entropy is Mathlib's `klDiv`, valued in $[0,\infty]$; the real bounds are compared after embedding.
--
--   Differences from the source:
--   - encoding: $\mathrm{KL}(P_u\|P_v)$ real → `klDiv` in $[0,\infty]$ compared with $\mathrm{ofReal}$ of the (nonnegative) bounds; reason: Lean convention; same inequalities
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Lemma A.4, p.22

import Mathlib
import Definitions.Def_MetricMinTest_signedBernoulli

namespace MetricMinTest

/-- **Lemma A.4 (Signed Bernoulli bounds).** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Lemma A.4, p.22: "For
means u, v ∈ [−1/4, 1/4], ½(u − v)² ≤ KL(P_u‖P_v) ≤ (u − v)²/(1 − v²) ≤ (16/15)(u − v)² ≤ 2(u − v)²."

**Formalization Note.** `P_u` is `signedBernoulli u`; `KL` is Mathlib's `klDiv` (in `ℝ≥0∞`),
compared with `ENNReal.ofReal` of the real bounds, which are nonnegative. -/
theorem lemma_A_4 (u v : ℝ) (hu : u ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4))
    (hv : v ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)) :
    ENNReal.ofReal ((u - v) ^ 2 / 2) ≤
        InformationTheory.klDiv (signedBernoulli u) (signedBernoulli v) ∧
    InformationTheory.klDiv (signedBernoulli u) (signedBernoulli v) ≤
        ENNReal.ofReal ((u - v) ^ 2 / (1 - v ^ 2)) ∧
    (u - v) ^ 2 / (1 - v ^ 2) ≤ 16 / 15 * (u - v) ^ 2 ∧
    16 / 15 * (u - v) ^ 2 ≤ 2 * (u - v) ^ 2 := by sorry

end MetricMinTest
