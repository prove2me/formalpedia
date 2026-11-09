-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_theorem_1_1
-- name    : MemOracleLB.Optimization.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:03.456363+00:00
-- url     : https://prove2.me/theorems/ea2b82af-f4e1-4ddb-9a95-541e3f0fc0a3
-- title:
--   Theorem 1.1 — Linear optimization (goal)
-- statement:
--   There exist absolute constants $a>0$, $C_0\ge1$ and $N\ge2$ with the following property. For every $C\ge C_0$, $n\ge N$ and randomized adaptive membership-query algorithm $A$ in dimension $n$, suppose that for every convex body $K$ with $B^n\subseteq K\subseteq Cn^{3/2}B^n$ and every unit objective $c$, with probability at least $2/3$ the algorithm halts with a positive output $Z$ satisfying
--
--   $$\tfrac12\operatorname{OPT}(K,c)\le Z\le\operatorname{OPT}(K,c)\quad\text{or}\quad\operatorname{OPT}(K,c)-n\le Z\le\operatorname{OPT}(K,c),\qquad\operatorname{OPT}(K,c)=\max_{x\in K}\langle c,x\rangle.$$
--
--   Then there is an admissible input $(K,c)$ for which both
--
--   $$\Pr\!\left(T\ge a\frac{n^2}{\log^2 n}\right)\ge\frac1{100},\qquad\mathbb ET\ge a\frac{n^2}{\log^2 n}.$$
--
--   Both conclusions use the same input. The seed space is an arbitrary probability space. The action is measurable in the seed for each fixed objective and finite answer history, with no joint measurability requirement in the objective. Nontermination has no successful output and costs $T=\infty$. The expectation is the nonnegative integral of that extended query count. The statement covers the full body class and permits every real query, every adaptive history, and arbitrary computation between queries.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - generalization: the printed Theorem 1.1 states an expectation lower bound → the same-input tail bound at probability 1/100 as well as the expectation bound; reason: the source explicitly states the tail assertion after Corollary 1.3 on PDF p.3 and proves the same-input bounds on PDF p.21
--   - reading: for a sufficiently large universal radius constant C → there exists C0 and the theorem holds for every C>=C0, uniformly; reason: the class increases with C, and an algorithm successful on the larger class also succeeds on the fixed smaller class
--   - encoding: a randomized adaptive membership-query algorithm and its expected cost → a measurable-seed action on all finite Boolean histories, exact oracle recursion, ENat query count and its nonnegative integral; reason: per-input measurability is the probability convention; infinite nontermination cost and arbitrary real queries preserve the complete algorithm class
--   - encoding: the standing sufficiently large absolute ambient dimension on PDF p.8 → an existential natural threshold N at least 2 before the dimension and all instance data; reason: this makes the source asymptotic quantifier explicit and keeps logarithms and denominators in their stated domains
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Theorem 1.1, PDF p. 2 (printed p. 1), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_OracleModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
universe u11

namespace MemOracleLB.Optimization

/-- Theorem 1.1, PDF p.2 (printed p.1), with the tail bound on PDF p.3 and proof on PDF p.21.
All algorithms, all bodies in the class, both approximation alternatives, and nontermination. -/
theorem theorem_1_1 : ∃ a C₀ : ℝ, 0 < a ∧ 1 ≤ C₀ ∧ ∃ N : ℕ, 2 ≤ N ∧
    ∀ C : ℝ, C₀ ≤ C → ∀ n : ℕ, N ≤ n →
    ∀ {Ω : Type u11} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (A : OracleAlgorithm n Ω),
      (∀ (K : Set (E n)), InClass C K → ∀ c : E n, ‖c‖ = 1 →
        2 / 3 ≤ P {ω | Succeeds A K c ω}) →
      ∃ (K : Set (E n)) (c : E n), InClass C K ∧ ‖c‖ = 1 ∧
        1 / 100 ≤ P {ω | ENNReal.ofReal (a * (n : ℝ) ^ 2 / (Real.log n) ^ 2) ≤
          (queries A K c ω).toENNReal} ∧
        ENNReal.ofReal (a * (n : ℝ) ^ 2 / (Real.log n) ^ 2) ≤
          ∫⁻ ω, (queries A K c ω).toENNReal ∂P := by sorry

end MemOracleLB.Optimization
