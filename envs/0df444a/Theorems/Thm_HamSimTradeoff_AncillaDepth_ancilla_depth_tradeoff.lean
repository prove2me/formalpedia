-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_ancilla_depth_tradeoff
-- name    : HamSimTradeoff.AncillaDepth.ancilla_depth_tradeoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:11.690188+00:00
-- url     : https://prove2.me/theorems/d2fb547d-1da0-45c0-b399-35e6b182f578
-- title:
--   Theorem 1.1 — ancilla-depth tradeoff (corrected: +1 inside both O(·) bounds)
-- statement:
--   There is an absolute constant $C>0$ with the following property. For any fixed integer $L\ge2$, any coherent Suzuki architecture with $k,s\ge1$, $a\ge0$, positive refinements and arbitrary unitary controllers, and any $\varepsilon\in(0,1/2)$, suppose $\eta\ne0$ and
--   $$\|C(t)-\eta e^{-itA}\|\le\varepsilon$$
--   for every system dimension $d\ge1$, every Hermitian decomposition $A=\sum_{j=1}^{L}\alpha_jH_j$ with $\alpha_j>0$, $\sum_j\alpha_j=1$, $H_j^2=I$, and every real $|t|\le1$. Then
--   $$\log(1/\varepsilon)\le C\bigl(1+(k+s2^a)\log(s2^aQ)+\log(1/|\eta|)\bigr).$$
--   Moreover, for every $c_0,c_1>0$ there is $C'>0$, depending only on $c_0,c_1$, such that all the same hypotheses and
--   $$s2^a\le Q^{c_0},\qquad |\eta|\ge Q^{-c_1}$$
--   imply
--   $$\log(1/\varepsilon)\le C'\bigl(1+(\log Q)^2+s2^a\log Q\bigr).$$
--   Here $Q$ is normalized depth and $\eta$ is the ideal controller amplitude determined by the architecture. Both conclusions are part of this single target. They constrain every architecture that achieves Hamiltonian-independent accuracy, including zero ancillary qubits and depth one.
--
--   **Formalization Note** The paper writes $O(\cdot)$; the Lean states an absolute constant $C$ chosen before all parameters. In the second clause $C'$ is chosen after $c_0,c_1$ only and before the architecture, $L$, and $\varepsilon$. Matrix norms are spectral; logarithms are natural. The correction's counterexample satisfies every printed assumption and removes no regime.
--
--   Differences from the source:
--   - correction: (1.9) and (1.10) omit an additive constant inside O(·) → +1 inside both O(·) expressions; reason: at L=2, k=s=m=1, a=0, V=I, Q=η=1, Strang error is ≤2/27<1/10 for every decomposition and |t|≤1; ε=1/10 meets all assumptions but the printed bounds assert log 10≤0
--   - reading: Q = D/L = Θ(5^{k−1}∑ℓ max_r mℓr) → Q = 5^{k−1}∑ℓ max_r mℓr exactly; reason: this is the displayed representative used by the proof, preserving the asymptotic resource scale
--   - encoding: O(·) or exp(−O(·)) with an absolute hidden constant → a positive real constant chosen before all other parameters; reason: the proof supplies no numeral; quantifier order enforces uniformity
--   - reading: every decomposition with L≥2, parameters may depend on L → L fixed per architecture, with every positive system dimension and every L-term decomposition; reason: the standing convention p.5 allows dependence on L; the architecture is fixed before all weights and matrices
--   - encoding: indices 1,…,L, rounds 1,…,s and branches 1,…,R → zero-based Fin indices, with ancilla |0^a⟩ represented by index zero; reason: a bijective relabeling preserves every matrix product and sum
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), p.5, Theorem 1.1, both Eqs. (1.9)–(1.10); model pp.4–5; +1 correction documented in local paper.md §Correction

import Definitions.Def_HamSimTradeoff_AncillaDepth_Response
import Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth

/-- Theorem 1.1, both clauses. Corrected: +1 inside each O(·) at Q=1.
At L=2, k=s=m=1, a=0, V=I, eta=Q=1, the Strang bound is at most
2/27 < 1/10 for every admissible decomposition and |t|≤1. The printed
bounds would assert log 10 ≤ 0. This correction excludes no architecture. -/
theorem ancilla_depth_tradeoff :
    (∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (B : Architecture) (eps : ℝ),
      2 ≤ L → 0 < eps → eps < 1 / 2 → eta B ≠ 0 → UniformApproximation B L eps →
      Real.log (1 / eps) ≤ C * (1 + ((B.k : ℝ) + (B.s * 2 ^ B.a : ℕ)) *
        Real.log ((B.s * 2 ^ B.a : ℕ) * depth B) + Real.log (1 / ‖eta B‖))) ∧
    (∀ c0 c1 : ℝ, 0 < c0 → 0 < c1 → ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (B : Architecture) (eps : ℝ),
        2 ≤ L → 0 < eps → eps < 1 / 2 → eta B ≠ 0 → UniformApproximation B L eps →
        (B.s * 2 ^ B.a : ℕ) ≤ (depth B) ^ c0 → (depth B) ^ (-c1) ≤ ‖eta B‖ →
        Real.log (1 / eps) ≤ C * (1 + (Real.log (depth B)) ^ 2 +
          (B.s * 2 ^ B.a : ℕ) * Real.log (depth B))) := by sorry

end HamSimTradeoff.AncillaDepth
