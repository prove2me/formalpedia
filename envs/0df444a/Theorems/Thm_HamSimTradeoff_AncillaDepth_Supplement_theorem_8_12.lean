-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_theorem_8_12
-- name    : HamSimTradeoff.AncillaDepth.Supplement.theorem_8_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:02:05.161626+00:00
-- url     : https://prove2.me/theorems/806a0f9a-c9cd-42d5-98c5-132b502df7a3
-- title:
--   Theorem 8.12 — normalized-trace estimation of f on the family A_x needs Ω(d) queries, d = deg~_ε(f), γ ≥ 2(1 − 2c)E_{d−1}
-- statement:
--   There is an absolute $C>0$ such that for every continuous $f:[-1,1]\to[-1,1]$, $0<\varepsilon\le1$, $c<1/2$, and $d=\widetilde{\deg}_\varepsilon(f)\ge1$ satisfying $E_d\le cE_{d-1}$, there exist real Jacobi diagonal entries and strictly positive cycle edges with endpoint spectra in $[-1,1]$. The resulting pair and bit family (8.3), (8.5) have
--   $$\gamma=\left|\frac1d\operatorname{Tr}f(A_0)-\frac1d\operatorname{Tr}f(A_\pi)\right|\ge2(1-2c)E_{d-1}>0.$$
--   Every general quantum query algorithm estimating $\tau_f(x)=d^{-1}\operatorname{Tr}f(A_x)$ within $\gamma/4$ with probability at least $2/3$ for every $x$ uses at least $Cd$ XOR queries. In particular, for every $e_0>0$ with $E_{d-1}\ge e_0$, estimating within $(1-2c)e_0/2$ also requires at least $Cd$ queries.
--   The family is chosen before the algorithm; no trace separation or Jacobi-existence premise is supplied. The model includes DQC1 algorithms. The paper writes Omega; Lean states an absolute constant C chosen before all parameters. This supplies the approximate-degree lower bound for normalized-trace estimation.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: O or Omega with uniform constants → positive constants quantified before every parameter over which they are uniform; reason: retains the paper's absolute constants or its indicated dependence on eta or r
--   - encoding: continuous f on [-1,1], periodic Jacobi matrices and normalized traces → real functions with ContinuousOn, additive cyclic-edge matrices, and real-part functional-calculus traces; reason: extensions outside the interval do not matter; endpoints are Hermitian contractions; d >= 1 excludes undefined normalization
--   - generalization: DQC1 estimation with bounded error → every finite-workspace quantum XOR-query algorithm with success probability at least 2/3 on every input; reason: purification puts each DQC1 computation inside this class; the parity lower bound applies to the larger class
--   - reading: In particular, if E_{d−1} = Ω(1), estimating τ_f(x) to constant additive error requires Ω(deg~_ε(f)) queries → for every e0 with 0 < e0 ≤ E_{d−1}, estimation within (1−2c)e0/2 needs at least C·d queries, same absolute C; reason: a constant lower bound e0 on E_{d−1} gives the constant error level (1−2c)e0/2 ≤ γ/4; the informal Ω(1) is read with its constant e0 explicit
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 38, Theorem 8.12

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Jacobi
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem theorem_8_12 : ∃ C : ℝ, 0 < C ∧
    ∀ f : ℝ → ℝ, IntervalFunction f → ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
    ∀ c : ℝ, c < 1/2 → ∀ d : ℕ, 1 ≤ d → d = approximateDegree f eps →
      bestError f d ≤ c*bestError f (d-1) →
    ∃ J : JacobiData d, JacobiBounded J ∧
      2*(1-2*c)*bestError f (d-1) ≤ traceGap f J ∧ 0 < traceGap f J ∧
      QueryLowerBound (traceFunction f J) (traceGap f J/4) (C*d) ∧
      (∀ e0 : ℝ, 0 < e0 → e0 ≤ bestError f (d-1) →
        QueryLowerBound (traceFunction f J) ((1-2*c)*e0/2) (C*d)) := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
