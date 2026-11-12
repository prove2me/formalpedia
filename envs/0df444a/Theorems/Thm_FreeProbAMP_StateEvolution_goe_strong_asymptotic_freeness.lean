-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_goe_strong_asymptotic_freeness
-- name    : FreeProbAMP.StateEvolution.goe_strong_asymptotic_freeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:29:00.128653+00:00
-- url     : https://prove2.me/theorems/b6b41c68-1f67-416f-9084-20bba4b2c25f
-- title:
--   Proposition 6.2 — GOE strong asymptotic freeness
-- statement:
--   Let $W_1^d,\ldots,W_k^d$ be independent standard normalized GOE matrices, independent of a deterministic or random self-adjoint complex matrix tuple $(B_1^d,\ldots,B_\ell^d)$. Suppose this tuple converges strongly in noncommutative distribution to $(b_1,\ldots,b_\ell)$ in a faithful tracial C*-probability space. Then there is a trace-preserving isometric extension containing standard freely independent semicircular variables $s_1,\ldots,s_k$, free from $(b_j)$, such that
--
--   $$(W_1^d,\ldots,W_k^d,B_1^d,\ldots,B_\ell^d)\xrightarrow{\rm str}(s_1,\ldots,s_k,b_1,\ldots,b_\ell).$$
--
--   The semicircular covariances are $\tau(s_is_j)=\mathbf1_{i=j}$. Strong convergence tests both trace and norm for every joint noncommutative polynomial, in probability. This is the independent-GOE input to the matrix update. The $B$ tuple may be random, with no independence across different dimensions required.
--
--   Differences from the source:
--   - encoding: positive matrix dimension d tends to infinity → natural index j represents physical dimension j+1; reason: bijection with all positive dimensions; n(j) remains arbitrary
--   - encoding: self-adjoint matrix tuples and noncommutative polynomials → Hermitian comparison matrices and complexified GOE inputs for scalar complex polynomial tests; reason: Definition 2.7 does not restrict comparison entries to reals; real symmetric instances embed with identical traces and operator norms
--   - encoding: adjoin semicircular variables to the limiting family → existence in an isometric trace-preserving C*-extension; reason: the original ambient algebra need not contain a new independent semicircular direction; no source law is changed
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 29, Proposition 6.2 ([FSW21], Theorem 4.3)

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_Terminal

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Proposition 6.2 ([FSW21]), submission p.29. The extension is in the conclusion. -/
theorem goe_strong_asymptotic_freeness
    {Ω B : Type*} [MeasurableSpace Ω] [CStarAlgebra B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : FaithfulTrace B) (k l : ℕ)
    (W : (d : ℕ) → Ω → Fin k → RMat (d+1))
    (A : (d : ℕ) → Ω → Fin l → CMat (d+1)) (b : Fin l → B)
    (hg : ∀ d, GOEArray μ (W d)) (hi : ∀ d, IndepFun (W d) (A d) μ)
    (hb : StrongComplex μ τ A b) :
    ∃ C : TraceExtension B τ, ∃ s : Fin k → C.carrier,
      JointSemicircular C.trace s ∧
      (∀ i j, C.trace.value (s i*s j) = if i=j then 1 else 0) ∧
      FreeFamilies C.trace s (fun j => C.embed (b j)) ∧
      StrongComplex μ C.trace (fun d ω => Sum.elim (fun i => complexify (W d ω i)) (A d ω))
        (Sum.elim s (fun j => C.embed (b j))) := by sorry

end FreeProbAMP.StateEvolution
