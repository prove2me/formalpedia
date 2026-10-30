-- Prove2me | Theorems.Thm_KhachiyanRounding_BCD_theorem2
-- name    : KhachiyanRounding.BCD.theorem2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:46:15.864159+00:00
-- url     : https://prove2.me/theorems/671ed666-4f34-47e7-aef0-5a0894eea82c
-- title:
--   Theorem 2 — arbitrary-input BCD rounding with arithmetic complexity
-- statement:
--   There are absolute constants $C,K>0$ such that for every $n\ge1$, every real family $a_1,\ldots,a_m\in\mathbb R^n$ with affine hull $\mathbb R^n$, and every $\varepsilon>0$, the fixed scalar program has a successful finite execution returning a center $b$ and positive-definite shape $Q$.
--
--   It uses the signed lift $\{\pm(a_j;1)\}$ and tolerance $\varepsilon'=n\varepsilon/(n+1)$. Its endpoint weights and caches satisfy the actual lifted relaxed optimality conditions. For aggregated weights $p_j=q_j^++q_j^-$, it returns
--   $$b=\sum_jp_ja_j,\quad C_p=\sum_jp_ja_ja_j^\mathsf T-bb^\mathsf T,\quad Q=((1+\varepsilon)n)C_p.$$
--   The aggregated weights are simplex weights; their block moment and covariance $C_p$ are positive definite. Its actual ellipsoid is precisely the source affine slice
--   $$E(b,Q)=\{x:(x;1)\in\sqrt{1+(1+\varepsilon)n}\,E'_p\}.$$
--   With $t=(1+\varepsilon)n$, both inclusions hold:
--   $$H_{b,1/t}(E(b,Q))\subseteq\operatorname{conv}\{a_j\}\subseteq E(b,Q).$$
--   The actual cost, including lift, tolerance formation, initialization, guarded inversion, every scalar update and comparison, and output construction, is bounded by the positive global expression
--   $$\mathrm{cost}\le C B_{\mathrm{lift}}(n,m,\varepsilon),\qquad B_{\mathrm{lift}}=2m(n+1)^2\left(\frac{n+1}{n\varepsilon}+\ln(n+1)+\ln\ln(2m)\right).$$
--   Furthermore, whenever $n\ge2$ or $m\ge3$, the same universal constants give
--   $$B_{\mathrm{lift}}\le Kmn^2(\varepsilon^{-1}+\ln n+\ln\ln m),\qquad \mathrm{cost}\le CKmn^2(\varepsilon^{-1}+\ln n+\ln\ln m).$$
--   The remaining size $n=1,m=2$ keeps the global cost bound and every geometric and termination conclusion for all $\varepsilon>0$. This makes the source asymptotic order explicit while preserving its full input domain. The theorem does not assume feasible iterates, a stopping witness, correct caches, or a precomputed rounding ellipsoid.
--
--   Differences from the source:
--   - generalization: a set of m points → an indexed family allowing repeated points; reason: every source set has a listing without repetition; repetitions preserve the geometric domain and only enlarge the input length in the budget
--   - encoding: Euclidean real coordinates and ellipsoids → Fin-indexed real arrays and the published inverse-shape ellipsoid, using homotheties about its center; reason: quadratic pairings use coordinate sums, not the default sup norm; the carrier and both inclusions are unchanged
--   - encoding: BCD computes an ellipsoid in arithmetic operations and comparisons → a fixed scalar implementation with first-maximum ties, guarded diagonal Gauss–Jordan, cached scores and fuel-indexed finite evaluation, together with explicit endpoint and shape conclusions; reason: these specify a legal implementation and its ordinary output data; no input instance is excluded and no certificate of the desired result is assumed
--   - encoding: N(ε)=O(mn²(ε⁻¹+ln n+ln ln m)) for the lifted computation → a positive global lifted budget on every input plus an explicit uniform comparison with the printed budget when n≥2 or m≥3; reason: this encodes the source asymptotic order without treating the negative logarithmic term at n=1,m=2 and large ε as an everywhere-positive budget; that input case retains execution, exact geometry and the full lifted cost bound
-- source:
--   Leonid G. Khachiyan (1996), Rounding of Polytopes in the Real Number Model of Computation, Mathematics of Operations Research 21(2), 307–320, https://doi.org/10.1287/moor.21.2.307, Theorem 2 and proof, printed p.317 / PDF p.12; standing affine-hull assumption (3.1), printed p.314 / PDF p.9; (3.2)–(3.7), printed pp.315–316 / PDF pp.10–11; (1.2)–(1.3), printed p.307 / PDF p.2.

import Definitions.Def_KhachiyanRounding_BCD_Specification

namespace KhachiyanRounding.BCD

/-- Khachiyan (1996), Theorem 2, printed p.317 / PDF p.12, with (3.1).
The lifted global budget covers n=1,m=2 and every ε>0. The second absolute
constant explicitly compares it with the printed order away from that finite
size exception; the exception retains the execution and geometric conclusions.
No supplied feasible iterate, convergence certificate or cost oracle occurs. -/
theorem theorem2 :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ), 1 ≤ n →
        affineSpan ℝ (Set.range a) = ⊤ → ∀ ε : ℝ, 0 < ε →
        ∃ (fuel : ℕ) (out : Output (Fin m ⊕ Fin m) (n + 1) n) (cost : ℕ),
          general a ε fuel 0 = some (out, cost) ∧
          EndpointCorrect (KhachiyanRound.BCD.liftPts a) out.endpoint
            ((n : ℝ) * ε / (n + 1 : ℕ)) ∧
          (let p := KhachiyanRound.BCD.aggr out.endpoint.weights
           p ∈ stdSimplex ℝ (Fin m) ∧
           (KhachiyanRound.BCD.blockMatrix a p).PosDef ∧
           (covariance a p).PosDef ∧
           out.center = ∑ j, p j • a j ∧
           out.shape = ((1 + ε) * (n : ℝ)) • covariance a p ∧
           out.shape.PosDef ∧
           LinearOptimization.ellipsoid out.center out.shape =
             KhachiyanRound.BCD.lemma5Ellipsoid a p ε) ∧
          Rounds a out.center out.shape ((1 + ε) * (n : ℝ)) ∧
          0 < liftedBudget n m ε ∧
          (cost : ℝ) ≤ C * liftedBudget n m ε ∧
          ((2 ≤ n ∨ 3 ≤ m) →
            liftedBudget n m ε ≤ K * printedBudget n m ε ∧
            (cost : ℝ) ≤ (C * K) * printedBudget n m ε) := by sorry

end KhachiyanRounding.BCD
