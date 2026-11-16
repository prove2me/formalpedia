-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_8_10
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_8_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:01:20.265952+00:00
-- url     : https://prove2.me/theorems/6c576f16-61ce-45f8-ad6f-527300875e6d
-- title:
--   Lemma 8.10 — the periodic Jacobi pair separates normalized traces: γ ≥ 2(E_{d−1} − η) − 2η = 2E_{d−1} − 4η
-- statement:
--   Let $f:[-1,1]\to[-1,1]$ be continuous, $0<\varepsilon\le1$, and $d=\widetilde{\deg}_\varepsilon(f)\ge1$. Write $E_n$ for the best degree-$n$ uniform approximation error. Let $J$ have real diagonal entries and strictly positive cycle edges, with $\|A_0\|,\|A_\pi\|\le1$, and discriminant $\Delta$ fixed by (8.4). Suppose $P$ is a best degree-$(d-1)$ approximant, $\sigma\in\{\pm1\}$, $E_d\le\eta<E_{d-1}$, and on the entire interval
--   $$f=P+\sigma(E_{d-1}-\eta)\Delta+r,\qquad |r|\le\eta.$$
--   For the same periodic Jacobi pair, put $\gamma=|d^{-1}\operatorname{Tr}f(A_0)-d^{-1}\operatorname{Tr}f(A_\pi)|$. Then
--   $$\gamma\ge2E_{d-1}-4\eta;\qquad \eta=E_d\ \Longrightarrow\ \gamma\ge2E_{d-1}-4E_d.$$
--   The decomposition assumptions of Proposition 8.9 are explicit; their existence is not assumed by Theorem 8.12. This lemma provides its trace gap.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: continuous f on [-1,1], periodic Jacobi matrices and normalized traces → real functions with ContinuousOn, additive cyclic-edge matrices, and real-part functional-calculus traces; reason: extensions outside the interval do not matter; endpoints are Hermitian contractions; d >= 1 excludes undefined normalization
--   - encoding: under the assumptions of Proposition 8.9 → TraceDecomposition lists its polynomial, sign, remainder and interval assumptions; reason: makes the imported assumptions explicit without assuming the trace gap
--   - generalization: Proposition 8.9: ‖A_θ‖ ≤ 1 (θ unspecified) → ‖A_0‖ ≤ 1 and ‖A_π‖ ≤ 1 only (JacobiBounded); reason: only the two boundary matrices enter the statement and the proof; every pair with ‖A_θ‖ ≤ 1 for all θ satisfies the weaker hypothesis
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 38, Lemma 8.10

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_TraceDecomposition
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_8_10 {d : ℕ} (hd : 1 ≤ d) (f : ℝ → ℝ) (hf : IntervalFunction f)
    (eps : ℝ) (heps : 0 < eps ∧ eps ≤ 1) (hdegree : d = approximateDegree f eps)
    (J : JacobiData d) (Delta P : Polynomial ℝ) (sigma eta : ℝ) (r : ℝ → ℝ)
    (hdecomp : TraceDecomposition f J Delta P sigma eta r) :
    2*bestError f (d-1)-4*eta ≤ traceGap f J ∧
    (eta = bestError f d → 2*bestError f (d-1)-4*bestError f d ≤ traceGap f J) := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
