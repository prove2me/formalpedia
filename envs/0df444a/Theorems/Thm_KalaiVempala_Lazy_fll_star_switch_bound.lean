-- Prove2me | Theorems.Thm_KalaiVempala_Lazy_fll_star_switch_bound
-- name    : KalaiVempala.Lazy.fll_star_switch_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:11.754428+00:00
-- url     : https://prove2.me/theorems/4a417d95-6e34-42f7-84ac-17fd6d28c742
-- title:
--   Proof of Lemma 1.2 (FLL* case), p. 304 — the probability of switching is at most ε|s_t|₁
-- statement:
--   **FLL\* rarely switches.** Let $\varepsilon > 0$, $v \in \mathbb R^n$, and let $\nu$ be any probability law of the current perturbation $p_t$. Perform one FLL\*($\varepsilon$) update with state $s_t = v$: with probability $\min\{1, d\mu(p_t - v)/d\mu(p_t)\}$ set $p_{t+1} = p_t - v$, otherwise $p_{t+1} = -p_t$. Then
--
--   $$\Pr\big[\, p_{t+1} \ne p_t - v \,\big] \;\le\; \varepsilon |v|_1 .$$
--
--   Since $s_{1:t} + p_{t+1} = s_{1:t-1} + p_t$ exactly when $p_{t+1} = p_t - s_t$, this bounds the probability that FLL\* has to change the point at which it calls the oracle; with $|s_t|_1 \le A$ it is at most $\varepsilon A$.
--
--   **Formalization Note** The probability is the measure of $\{(p, q) : q \ne p - v\}$ under the joint law `fllStarJoint ε v ν` of $(p_t, p_{t+1})$. The bound is stated for every probability law $\nu$ of $p_t$, which is stronger than the page's $p_t \sim \mu$; the page's argument is pointwise in $p_t$. The page writes the switching probability as $1 - d\mu(p_t + s_t)/d\mu(p_t)$; the algorithm's step 3(a) accepts $p_t - s_t$, so the switching probability is $1 - \min\{1, d\mu(p_t - s_t)/d\mu(p_t)\}$, which the statement uses. The bound $\varepsilon|s_t|_1$ holds either way.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 304, proof of Lemma 1.2 (FLL* case), last display ("the probability of switching is at most ...")

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Lazy_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Lazy

theorem fll_star_switch_bound {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v : Fin n → ℝ)
    (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν] :
    fllStarJoint ε v ν {q | q.2 ≠ q.1 - v} ≤ ENNReal.ofReal (ε * ∑ i, |v i|) := by sorry

end KalaiVempala.Lazy
