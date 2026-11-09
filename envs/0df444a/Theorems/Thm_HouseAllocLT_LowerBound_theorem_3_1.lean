-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_theorem_3_1
-- name    : HouseAllocLT.LowerBound.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:40.295468+00:00
-- url     : https://prove2.me/theorems/be8ba27d-5368-424c-809e-29cc148a64c9
-- title:
--   Theorem 3.1 — finite, asymptotic and uniform LT lower bounds
-- statement:
--   For every $n\ge2$ and every lexicographically truthful randomized mechanism $\phi$ on the full domain of $n$ agents and $n$ objects,
--
--   $$\alpha_{n,n}(\phi)\ge\frac{n-\sqrt{n\ln(n+1)/2}}{B_n}.\tag{7}$$
--
--   Every sequence $(\phi_n)$ of such LT mechanisms satisfies
--
--   $$\liminf_{n\to\infty}\alpha_{n,n}(\phi_n)\ge\frac e{e-1}.\tag{8}$$
--
--   Every family $\phi$ defined and LT at all positive market sizes satisfies
--
--   $$\alpha(\phi)\ge\frac e{e-1}.$$
--
--   Reports may contain ties, omit objects, or be empty. No anonymity, determinism or Pareto-optimality assumption is made. The benchmark is the rank-maximal signature, and all three clauses are asserted together.
--
--   Differences from the source:
--   - encoding: agents, objects and ranks numbered from one → Fin indices numbered from zero; reason: the bijection sends each code index j to the source index j+1
--   - encoding: lottery on feasible matchings → real probability vector on finite edge sets with feasible support; reason: these encode exactly the same distributions, including irrational weights
--   - encoding: ratios taking values in the nonnegative extended reals → ENNReal ratios and ENNReal liminf, with ofReal applied to the real lower bounds; reason: positive numerator divided by zero is infinity in both conventions
--   - encoding: mechanisms at every positive market size and sequence indexed from n at least two → families total also at zero sizes, with LT required only at the source sizes; reason: zero-size mechanisms have the unique empty output; omitted finite initial terms do not affect the liminf or the positive-size supremum
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Theorem 3.1, equations (7), (8) and uniform-ratio clause, PDF p. 9 (printed p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_prefixList

open scoped BigOperators ENNReal Topology
open Filter

namespace HouseAllocLT.LowerBound

/-- Theorem 3.1, PDF p.9 (printed p.7): all of (7), (8), and the uniform
ratio consequence. Mechanisms and truthfulness use the full weak-order domain. -/
theorem theorem_3_1 :
    (∀ (n : ℕ), 2 ≤ n → ∀ φ : Mechanism n n, IsLT φ →
      ENNReal.ofReal (((n : ℝ) - deviationBound n) / B n) ≤ approximationRatio φ) ∧
    (∀ φ : (∀ n : ℕ, Mechanism n n), (∀ n, 2 ≤ n → IsLT (φ n)) →
      lowerBoundConstant ≤ Filter.liminf (fun n => approximationRatio (φ n)) atTop) ∧
    (∀ φ : MechanismFamily, (∀ n m, 1 ≤ n → 1 ≤ m → IsLT (φ n m)) →
      lowerBoundConstant ≤ uniformRatio φ) := by sorry

end HouseAllocLT.LowerBound
