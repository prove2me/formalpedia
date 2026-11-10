-- Prove2me | Theorems.Thm_HGASUndecidable_Main_theorem_10_1
-- name    : HGASUndecidable.Main.theorem_10_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:19:46.251766+00:00
-- url     : https://prove2.me/theorems/37b270bf-cf1f-4959-b011-d50329703c6b
-- title:
--   Theorem 10.1 — computable homogeneous F of degree E = D + 2(k+1) on R^{1+Σn_i} with GAS ⇔ β(Φ_X|K, a) < 0
-- statement:
--   Theorem 10.1 (From a maximal invariant average to GAS). Let k ≥ 1, n1, . . . , nk ≥ 1, K = S^{n1−1} × · · · × S^{nk−1} ⊆ R^{n1} × · · · × R^{nk}, let X = (X1, . . . , Xk) be a polynomial vector field with rational coefficients which is tangent to K at every point of K, and let a be a polynomial with rational coefficients. Let D ≥ 3 be odd with D ≥ deg X and D − 1 ≥ deg a, and put L = k + 1 and E = D + 2L. Then one can compute from (X, a, D) a homogeneous polynomial vector field F on R^{1+n1+···+nk} of degree E with rational coefficients such that 0 is GAS for v̇ = F(v) ⇐⇒ β(Φ_X|K, a) < 0. (10.1)
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: unique maximal solutions, with existence for all forward times included in stability → HasDerivWithinAt on [0,∞), explicit forward existence, and convergence of every forward solution; reason: polynomial fields are locally Lipschitz, so uniqueness and continuation make these formulations equivalent
--   - encoding: one fixed reasonable code for rational homogeneous polynomial vector fields → Encodable encoding of (dimension, declared degree, finite coordinate/exponent-list/rational-coefficient triples), with normalized support validation; reason: all rational fields have such finite representations; duplicate monomials are combined and invalid codes are negative instances
--   - encoding: Turing-machine recursive enumerability and total computability → Mathlib REPred, ComputablePred, Computable, and ManyOneReducible using partial recursive functions; reason: these are equivalent computability notions under effective translations
--   - encoding: the continuous ODE flow on the indicated invariant compact set → existence of a Flow ℝ on that set and the assertion for every Flow whose orbits have the prescribed derivative; reason: the source establishes existence and uniqueness; the relational presentation avoids an opaque ODE-flow constructor and includes existence in the conclusion
--   - encoding: the maximum invariant average and maximum finite-time orbit integral → real suprema over invariant Borel probability measures and initial states, respectively; reason: compactness, continuity and nonemptiness in the source guarantee attainment and boundedness; no maximization is over arbitrary noninvariant measures
--   - encoding: a product of k coordinate spaces and input (X,a,D) → consecutive blocks of a Euclidean vector and a natural-number encoding including the dimension list, D, and rational coefficient lists; reason: the block norms and tangency conditions are exactly those of the source; one total computable map is chosen for each fixed list of dimensions
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Theorem 10.1, printed p. 67 (PDF 69)

import Definitions.Def_HGASUndecidable_Main_SphereCodes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem theorem_10_1 {k : ℕ} (hk : 1 ≤ k) (dims : Fin k → ℕ) (hn : ∀ i, 1 ≤ dims i) :
    ∃ f : ℕ → ℕ, Computable f ∧
    ∀ (X : Fin (∑ i, dims i) → QPoly (∑ i, dims i)) (a : QPoly (∑ i, dims i)) (D : ℕ),
      tangentProduct dims X → 3 ≤ D → Odd D →
      (∀ i, (X i).totalDegree ≤ D) → a.totalDegree ≤ D-1 →
      (∃ Φ : Flow ℝ (sphereProduct dims), FlowSolves (sphereProduct dims) (evalQField X) Φ) ∧
      ∃ c : RawFieldCode, decodeField (f (sphereInputCode dims D X a)) = some c ∧
        ValidCode c ∧ c.1 = 1+(∑ i, dims i) ∧ c.2.1 = D+2*(k+1) ∧
        ∀ Φ : Flow ℝ (sphereProduct dims), FlowSolves (sphereProduct dims) (evalQField X) Φ →
          (GAS (codeField c) ↔ beta Φ (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x.val a) < 0) := by sorry

end HGASUndecidable.Main
