-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_proposition_8_11
-- name    : HamSimTradeoff.AncillaDepth.Supplement.proposition_8_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:01:44.30044+00:00
-- url     : https://prove2.me/theorems/c0638941-dd45-40db-97a7-79e99fd7edc8
-- title:
--   Proposition 8.11 — a γ-separated periodic Jacobi pair makes γ/4-estimation of τ_f(x) cost Ω(d) queries (parity reduction)
-- statement:
--   There is an absolute $C>0$ with the following property. For every $d\ge1$, continuous $f:[-1,1]\to[-1,1]$ and periodic Jacobi data with positive cycle edges and endpoint spectra in $[-1,1]$, form the bit family $A_x$ using those same coefficients in (8.5), and put $\tau_f(x)=d^{-1}\operatorname{Tr}f(A_x)$. If $\gamma=|\tau_f(0)-d^{-1}\operatorname{Tr}f(A_\pi)|>0$, then
--   $$T\ge Cd$$
--   for every quantum query algorithm that estimates $\tau_f$ within $\gamma/4$ with probability at least $2/3$ on every bit string $x\in\{0,1\}^d$. The algorithm may use any finite workspace, input-independent starting unit vector and interleaving unitaries, with the standard XOR oracle. This includes the paper's DQC1 model. The paper writes Omega; Lean states an absolute constant C chosen before all parameters. This lower bound is the query-complexity support for the trace-estimation companion theorem.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: O or Omega with uniform constants → positive constants quantified before every parameter over which they are uniform; reason: retains the paper's absolute constants or its indicated dependence on eta or r
--   - encoding: continuous f on [-1,1], periodic Jacobi matrices and normalized traces → real functions with ContinuousOn, additive cyclic-edge matrices, and real-part functional-calculus traces; reason: extensions outside the interval do not matter; endpoints are Hermitian contractions; d >= 1 excludes undefined normalization
--   - generalization: DQC1 estimation with bounded error → every finite-workspace quantum XOR-query algorithm with success probability at least 2/3 on every input; reason: purification puts each DQC1 computation inside this class; the parity lower bound applies to the larger class
--   - generalization: the periodic Jacobi pair A_0, A_π supplied by Proposition 8.9 → any periodic Jacobi data with positive edges and ‖A_0‖, ‖A_π‖ ≤ 1; reason: the parity reduction uses only (8.8)–(8.9) and γ > 0; the Proposition 8.9 pair is an instance
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 38, Proposition 8.11

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Jacobi
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem proposition_8_11 : ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ, 1 ≤ d → ∀ f : ℝ → ℝ, IntervalFunction f →
    ∀ J : JacobiData d, JacobiBounded J → 0 < traceGap f J →
      QueryLowerBound (traceFunction f J) (traceGap f J/4) (C*d) := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
