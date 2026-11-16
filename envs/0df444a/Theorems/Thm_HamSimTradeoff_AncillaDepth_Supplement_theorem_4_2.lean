-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_theorem_4_2
-- name    : HamSimTradeoff.AncillaDepth.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:52:23.736497+00:00
-- url     : https://prove2.me/theorems/dc5be86b-d0f2-4399-a2b4-c2d5035a0e30
-- title:
--   Theorem 4.2 — a one-round, k = 1, a = ⌈log m⌉ coherent Suzuki circuit with error ε, η = 1/σ_m = Ω(1/log m) and Q = O(m² log(m) ε^{−1/(2m)})
-- statement:
--   There is an absolute $C>0$ such that, for every integer $m\ge2$ and $0<\varepsilon<1/2$, a coherent Suzuki architecture can be chosen from $m,\varepsilon$ alone. It has $s=k=1$, $a=\lceil\log_2m\rceil$ and real coefficients chosen from $m$ alone, $c_1,\ldots,c_m$ with $\sum_jc_j=1$. Write $\sigma_m=\sum_j|c_j|$. Its success amplitude is the positive real $\eta=1/\sigma_m$, and
--   $$\eta\ge\frac1{C\log m},\qquad Q\le C m^2\log(m)\varepsilon^{-1/(2m)},\qquad \|C(t)-\eta e^{-itA}\|\le\varepsilon.$$
--   The error holds for every number of terms $L$, every positive system dimension, every Hermitian family with $\sum_j\|H_j\|\le1$, and every real $|t|\le1$. All $2^a$ branches have positive integer refinements, including unused branches. This gives a matching construction within the goal's architecture. The paper writes O and Omega; Lean states an absolute constant C chosen before all parameters.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: O or Omega with uniform constants → positive constants quantified before every parameter over which they are uniform; reason: retains the paper's absolute constants or its indicated dependence on eta or r
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 21, Theorem 4.2

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Hamiltonian
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem theorem_4_2 : ∃ C : ℝ, 0 < C ∧
    ∀ m : ℕ, 2 ≤ m → ∃ coeff : Fin m → ℝ,
      (∑ j, coeff j) = 1 ∧ 0 < (∑ j, |coeff j|)⁻¹ ∧
      1 / (C * Real.log m) ≤ (∑ j, |coeff j|)⁻¹ ∧
      ∀ eps : ℝ, 0 < eps → eps < 1/2 → ∃ B : Architecture,
        B.s = 1 ∧ B.k = 1 ∧ B.a = roundAncillas m ∧ m ≤ 2^B.a ∧
        eta B = (((∑ j, |coeff j|)⁻¹ : ℝ) : ℂ) ∧
        depth B ≤ C * (m:ℝ)^2 * Real.log m * eps^(-1/(2*(m:ℝ))) ∧
        HamiltonianApprox B eps := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
