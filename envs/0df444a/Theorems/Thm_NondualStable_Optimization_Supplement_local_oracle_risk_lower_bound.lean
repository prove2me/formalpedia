-- Prove2me | Theorems.Thm_NondualStable_Optimization_Supplement_local_oracle_risk_lower_bound
-- name    : NondualStable.Optimization.Supplement.local_oracle_risk_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:36:11.979136+00:00
-- url     : https://prove2.me/theorems/5a4154a0-471b-4557-ad3a-42615aafcd48
-- title:
--   Theorem 13 — Randomized local-oracle minimax lower bound
-- statement:
--   Fix $1\le p,q\le\infty$, with $1/\infty=0$, and write $q^*=(1-1/q)^{-1}$. There exists one constant $c_{p,q}\in(0,1/2)$, depending only on $p,q$, such that the following holds uniformly in every dimension $d\ge1$, positive scales $G,R$, and integer $1\le T\le c_{p,q}d$. For every local oracle $\mathcal O$ for the class of globally convex, finite real objectives whose global subgradients on $RB_p^d$ all belong to $GB_{q^*}^d$,
--   $$
--   \operatorname{Risk}_T\big(\mathcal O,\mathcal F(RB_p^d,GB_{q^*}^d)\big)\ge c_{p,q}GR\begin{cases}
--   T^{-1/p+(1/q-1/2)_+},&p<q,\\
--   d^{1/q-1/p}T^{-1/\max\{q,2\}},&q\le p<\infty,\\
--   1,&p=\infty.
--   \end{cases}
--   $$
--   The same constant controls the allowed query horizon and the lower bound. Algorithms may use arbitrary internal randomization and computation; they query and output feasible points, and make at most $T$ actual oracle calls for every objective and every seed. The risk takes the infimum over algorithms, the supremum over a fixed objective, and expectation over algorithm randomness only.
--
--   This companion theorem supplies the lower-bound comparison for the existing optimization goal. It is not used in the proof of Theorem 3. It includes $q=1$, $p=q=1$, and both infinity endpoints, with no logarithmic loss.
--
--   Differences from the source:
--   - encoding: real coordinate vectors, exponents in [1, infinity], and the global convex subdifferential → Fin d to real vectors, ENNReal norm exponents, and the published convex subdifferential via the Euclidean coordinate equivalence; reason: the coordinate equivalence preserves the standard pairing, finite real values make the domain guard automatic, and reciprocal infinity is zero
--   - encoding: arbitrary randomized adaptive algorithms with at most T queries for every instance and seed → probability mixtures of feasible decision trees of depth at most T, with almost everywhere measurable outputs and losses; reason: unrolling causal history rules preserves all executions, early stops and unqueried outputs; unreachable histories can be completed by a feasible output, and measurability is the standing convention for expectations
--   - encoding: expected real loss f(output) minus the constrained infimum, with infimum over algorithms and supremum over objectives → nonnegative gap as a supremum of positive improvements, integrated and optimized in ENNReal; reason: finite convex functions attain their minimum on the nonempty compact norm ball and have bounded loss there, so the values and inequality are unchanged without totalized real extrema
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 13 / PDF p. 14, Theorem 13; proof printed pp. 30–31 / PDF pp. 31–32, Appendix H, equation (43) and all three cases

import Mathlib
import Definitions.Def_NondualStable_Optimization_Supplement_FunctionClass
import Definitions.Def_NondualStable_Optimization_Supplement_MinimaxRisk

open scoped ENNReal

namespace NondualStable.Optimization.Supplement

/-- Theorem 13, STOC 2027 submission #415, printed p.13/PDF p.14.
The same c controls the horizon and the risk, before all instance and oracle data. -/
theorem local_oracle_risk_lower_bound (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (G R : ℝ), 0 < G → 0 < R →
      ∀ (T : ℕ), 1 ≤ T → (T : ℝ) ≤ c * (d : ℝ) →
      ∀ (Reply : Type) (O : LocalOracle
        (functionClass (ball p R : Set (Vec d)) (ball (dual q) G)) Reply),
      ENNReal.ofReal (c * G * R * lowerProfile p q d T) ≤
        minimaxRisk (ball p R) (functionClass (ball p R) (ball (dual q) G)) O T := by sorry

end NondualStable.Optimization.Supplement
