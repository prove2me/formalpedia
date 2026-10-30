-- Prove2me | Theorems.Thm_KhachiyanRounding_BCD_theorem1
-- name    : KhachiyanRounding.BCD.theorem1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:45:16.937379+00:00
-- url     : https://prove2.me/theorems/4817a1aa-04ee-4633-b9d3-bd169bebe434
-- title:
--   Theorem 1 — symmetric BCD rounding with arithmetic complexity
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every dimension $d\ge2$, every centrally symmetric real family $v_1,\ldots,v_M\in\mathbb R^d$ with affine hull $\mathbb R^d$, and every tolerance $\delta>0$.
--
--   The fixed scalar BCD implementation has a successful finite execution. If $p$ is its final weights and $Q$ its returned shape, then $p\in S_F$, the cached inverse and leverages are correct, $w_j(p)\le(1+\delta)d$ for every $j$, and $Q=((1+\delta)d)A(p)$ is positive definite. The returned center is zero. Writing $E=E(0,Q)$, its actual output satisfies
--   $$H_{0,1/\sqrt{(1+\delta)d}}(E)\subseteq\operatorname{conv}\{v_j\}\subseteq E,$$
--   and its actual charged cost satisfies
--   $$\mathrm{cost}\le C M d^2\left(\delta^{-1}+\ln d+\ln\ln M\right).$$
--
--   The cost includes uniform initialization, moment construction, guarded elimination, initial leverage computation, every scan and stopping test, every cached update, and final shape construction. The constant is independent of dimensions, coordinates, tolerance and evaluation fuel. Finite execution is asserted, not assumed. This is the full symmetric computation guarantee used in the arbitrary-input rounding theorem.
--
--   Differences from the source:
--   - generalization: a set of m points → an indexed family allowing repeated points; reason: every source set has a listing without repetition; repetitions preserve the geometric domain and only enlarge the input length in the budget
--   - encoding: Euclidean real coordinates and ellipsoids → Fin-indexed real arrays and the published inverse-shape ellipsoid, using homotheties about its center; reason: quadratic pairings use coordinate sums, not the default sup norm; the carrier and both inclusions are unchanged
--   - encoding: BCD computes an ellipsoid in arithmetic operations and comparisons → a fixed scalar implementation with first-maximum ties, guarded diagonal Gauss–Jordan, cached scores and fuel-indexed finite evaluation, together with explicit endpoint and shape conclusions; reason: these specify a legal implementation and its ordinary output data; no input instance is excluded and no certificate of the desired result is assumed
-- source:
--   Leonid G. Khachiyan (1996), Rounding of Polytopes in the Real Number Model of Computation, Mathematics of Operations Research 21(2), 307–320, https://doi.org/10.1287/moor.21.2.307, Theorem 1, printed p.314 / PDF p.9; standing assumptions (2.1)–(2.2), printed p.309 / PDF p.4; rounding (1.4), printed p.308 / PDF p.3.

import Definitions.Def_KhachiyanRounding_BCD_Specification

namespace KhachiyanRounding.BCD

/-- Khachiyan (1996), Theorem 1, printed p.314 / PDF p.9, with the §2
standing assumptions on p.309 / PDF p.4. Finite execution, cached-score
correctness, genuine enclosing ellipsoid, both rounding inclusions and the
actual scalar cost are asserted together. Constants precede all inputs. -/
theorem theorem1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d M : ℕ) (v : Fin M → Fin d → ℝ),
      2 ≤ d → KhachiyanRound.BCD.IsCentrallySymmetric v →
      affineSpan ℝ (Set.range v) = ⊤ → ∀ δ : ℝ, 0 < δ →
      ∃ (fuel : ℕ) (out : Output (Fin M) d d) (cost : ℕ),
        symmetric v δ fuel 0 = some (out, cost) ∧
        EndpointCorrect v out.endpoint δ ∧
        out.center = 0 ∧
        out.shape = ((1 + δ) * (d : ℝ)) •
          KhachiyanRound.BCD.momentMatrix v out.endpoint.weights ∧
        out.shape.PosDef ∧
        Rounds v out.center out.shape (Real.sqrt ((1 + δ) * (d : ℝ))) ∧
        (cost : ℝ) ≤ C * printedBudget d M δ := by sorry

end KhachiyanRounding.BCD
