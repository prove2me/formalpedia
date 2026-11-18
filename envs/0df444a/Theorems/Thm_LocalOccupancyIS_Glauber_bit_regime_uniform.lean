-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_bit_regime_uniform
-- name    : LocalOccupancyIS.Glauber.bit_regime_uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:22:30.29705+00:00
-- url     : https://prove2.me/theorems/20114669-70b2-41c0-a608-69ee2fde191f
-- title:
--   Uniform rational-input Glauber guarantee in the explicit occupancy regime
-- statement:
--   Let $G$ be a finite graph of actual maximum degree $\Delta\ge1$, with hereditary neighborhood biclique density at most a nonnegative rational $b$ for biclique size $t\ge1$. Put $D=\log(\Delta/(b+1)^{1/(2t-1)})$ and $C=4(16e+3)$. Suppose
--
--   $$D\ge1000et,\qquad\frac{t\log D}{D}\le\frac1C.$$
--
--   There is an absolute constant $B\ge10^6$, preceding $n,\Delta,t,G,b$ and the supplied neighborhood orders, such that the prescribed rational-input procedure satisfies the full implementation conclusion with error coefficient $(C+2)t$ and common runtime exponent $1000$.
--
--   In particular, from every supplied initial independent set, its output at failure parameter $m\ge1$ satisfies
--
--   $$\Pr\!\left[|I_{\rm out}|\ge\left(1-(C+2)\frac{t\log D}{D}\right)\frac{nD}{\Delta}\right]\ge1-e^{-m},$$
--
--   and its charged expected bit cost is at most
--
--   $$B\bigl(n+\operatorname{ratBits}(b)+m+\operatorname{bits}(t)+1\bigr)^{1000}.$$
--
--   The full conclusion also includes the first terminating preprocessing stage, its enclosure and rounding guarantees, the fugacity perturbation estimate, the recomputed three-sweep local-occupancy certificate and finite-time bound, and exact equality of the fair-bit output law with the specified amplified Glauber law. This uniform regime implication supplies both the fixed-parameter and growing-parameter rational clauses of Corollary 4 and Remark 1.
-- source:
--   Davies and Tan, Large independent sets via neighborhood block dynamics, Glauber dynamics, and local occupancy, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf, Corollary 4 and Remark 1 p.6, Proposition 6, §§4–6 pp.13–20; quantitative rational-machine conventions in the mission BitExecution and GoalInterface definitions.

import Definitions.Def_LocalOccupancyIS_Glauber_GoalInterface

namespace LocalOccupancyIS.Glauber
theorem bit_regime_uniform :
    ∃ B : ℝ, 1000000 ≤ B ∧
      ∀ n Δ t : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      ∀ b : ℚ, 1 ≤ Δ → 1 ≤ t → 0 ≤ b → MaximumDegree G Δ → HereditaryDensity G t b →
      1000*Real.exp 1*t ≤ D Δ t (b:ℝ) →
      relativeError Δ t (b:ℝ) ≤ 1/(4*(16*Real.exp 1+3)) →
      ∀ w : Fin n → List (Fin n), (∀ u, IsSweep (G.neighborFinset u) (w u)) →
        BitConclusion G Δ t b w ((4*(16*Real.exp 1+3)+2)*t) B 1000 := by sorry
end LocalOccupancyIS.Glauber
