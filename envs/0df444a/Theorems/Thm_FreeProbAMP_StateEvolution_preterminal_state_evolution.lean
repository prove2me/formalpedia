-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_preterminal_state_evolution
-- name    : FreeProbAMP.StateEvolution.preterminal_state_evolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:46.372699+00:00
-- url     : https://prove2.me/theorems/ccd59005-c639-4da0-b387-e1bf6475f0b6
-- title:
--   Theorem 6.1 — state evolution before the terminal query
-- statement:
--   Under Assumptions 2.1–2.5, let $T\ge1$ be fixed and let the AMP trajectory be computed from independent normalized GOE matrices with $2n(d)/d^2\to\alpha>0$. Initialization may be arbitrary and dependent across its coordinates, independently of the Gaussian input, with its prescribed almost-sure all-moment empirical limit. Then
--
--   $$(u_i^0,\ldots,u_i^{T+1},m_i^0,\ldots,m_i^T)_{i\le n(d)}\xrightarrow{\rm emp}(U^0,\ldots,U^{T+1},G^0,\ldots,G^T),$$
--   $$(V^0,\ldots,V^T,M^0,\ldots,M^T)\xrightarrow{\rm str}(S^0,\ldots,S^T,W^0,\ldots,W^T),$$
--
--   where $G^t=g_t(U^0,\ldots,U^t)$, $W^t=\sum_{s\le t}a_{t,s}S^s$, and the Gaussian–semicircular covariances obey (2.4)–(2.5). Both convergence notions are in probability. This supplies the complete preterminal trajectory, including the additional vector iterate $u^{T+1}$.
--
--   Differences from the source:
--   - encoding: positive matrix dimension d tends to infinity → natural index j represents physical dimension j+1; reason: bijection with all positive dimensions; n(j) remains arbitrary
--   - encoding: self-adjoint real matrix tuples and noncommutative polynomials → real matrices are complexified for scalar complex polynomial tests; reason: all source polynomials and Euclidean operator norms are preserved
--   - encoding: the recursively specified Gaussian–semicircular limiting process → arbitrary probability/C*-space realizations satisfying precisely the state law; reason: finite Gaussian covariance and semicircular Fock realizations exist and have identical moments and faithful norms
--   - encoding: sample sizes n(d) with n(d) → ∞ → n(d) ≥ 1 for every d; reason: nondegeneracy only; at n = 0 the source's 1/n and n^{-1/2} normalizations are undefined, and n(d) → ∞ leaves only finitely many such d, which no limit statement sees
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 29, Theorem 6.1, (6.1)–(6.2)

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Theorem 6.1, submission p.29; includes u^{T+1}. -/
theorem preterminal_state_evolution
    {Ω E B : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [CStarAlgebra B]
    (D : FiniteData Ω) (L : LimitData E B) (T : ℕ) (α : ℝ) (hT : 1 ≤ T)
    (hA : AMPAssumptions D L T α) (hL : StateLaw L T α D.a D.g) :
    Empirical D.μ L.ν D.n (vectorTuple D (T+2) (T+1)) (limitTuple D L (T+2) (T+1)) ∧
    Strong D.μ L.τ (matrixTuple D (T+1)) (matrixLimit D L (T+1)) := by sorry

end FreeProbAMP.StateEvolution
