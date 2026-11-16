-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_theorem_6_4
-- name    : HamSimTradeoff.AncillaDepth.Supplement.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:00:32.654451+00:00
-- url     : https://prove2.me/theorems/db0be9df-6451-4913-a580-e7865f0e7120
-- title:
--   Theorem 6.4 — single-ancilla (π/2, 1, ε)-block encoding of a Hermitian A, ∥A∥ ≤ 1, from O(log(1/ε)) uses of controlled e^{±iA}
-- statement:
--   There is an absolute $C>0$ such that for every $0<\varepsilon<1$ one input-independent single-ancilla circuit can be chosen from $\varepsilon$ alone. Its queries are $c_0\!\operatorname{-}e^{iA}$ or $c_1\!\operatorname{-}e^{-iA}$, interleaved with arbitrary one-qubit unitaries. It uses $q$ queries and $q+1$ ancilla gates, with
--   $$q\le C(1+\log(1/\varepsilon)),\qquad dq+q+1\le Cd(1+\log(1/\varepsilon))\quad(d\ge1).$$
--   For every positive system dimension and every Hermitian $A$ with $\|A\|\le1$, the evaluated circuit is unitary and its success block $B$ satisfies
--   $$\|A-(\pi/2)B\|\le\varepsilon.$$
--   Thus it is a $(\pi/2,1,\varepsilon)$-block encoding, with depth $O(d\log(1/\varepsilon))$ on $0<\varepsilon<1/2$. The paper writes O; Lean states an absolute constant C chosen before all parameters. This companion result converts controlled evolution into a one-ancilla block encoding.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: O or Omega with uniform constants → positive constants quantified before every parameter over which they are uniform; reason: retains the paper's absolute constants or its indicated dependence on eta or r
--   - reading: O(d log(1/epsilon)) with no epsilon range stated → 0 < epsilon < 1 with C d (1+log(1/epsilon)); ancilla gates depend on epsilon alone; reason: the uniform oracle interpretation in the proof; for epsilon < 1/2 this implies the printed bound, while no-query scalar blocks cannot uniformly approximate both I and -I for epsilon < 1
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 31, Theorem 6.4

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_BlockEncoding
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

/-- The additive 1 records the epsilon-range reading for all 0<eps<1. -/
theorem theorem_6_4 : ∃ C : ℝ, 0 < C ∧
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∃ B : EvolutionCircuit,
      (B.q:ℝ) ≤ C*(1+Real.log (1/eps)) ∧
      (∀ d : ℕ, 1 ≤ d → (evolutionDepth B d:ℝ) ≤ C*d*(1+Real.log (1/eps))) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ A : Mat N, A.IsHermitian → ‖A‖ ≤ 1 →
        QAlgorithms.IsBlockEncoding (ancillaZero 1) (evolutionCircuit B A) (Real.pi/2) eps A := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
