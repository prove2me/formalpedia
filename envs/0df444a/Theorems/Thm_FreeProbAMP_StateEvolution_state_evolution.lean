-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_state_evolution
-- name    : FreeProbAMP.StateEvolution.state_evolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:38.631224+00:00
-- url     : https://prove2.me/theorems/1a72c4e5-301c-45fd-901a-c4ae46099b41
-- title:
--   Theorem 2.9 — strong state evolution with terminal-readout stability
-- statement:
--   Assume the normalized independent GOE input model and $2n(d)/d^2\to\alpha>0$. Initialization is independent of the Gaussian operators and converges almost surely, weakly with every moment, to $U^0$. For fixed $T\ge1$, let deterministic coefficients and nonlinearities satisfy Assumptions 2.3–2.5, and compute the actual AMP trajectory (1.4)–(1.6) with $M^{-1}=0$. Let $h:\mathbb R^{T+1}\to\mathbb R$ be any bounded Borel function whose discontinuity set has zero probability under $(U^0,\ldots,U^T)$. Set $\widehat m_i=h(u_i^0,\ldots,u_i^T)$ and $H=h(U^0,\ldots,U^T)$. Then
--
--   $$(u_i^0,\ldots,u_i^T,m_i^0,\ldots,m_i^T,\widehat m_i)_{i\le n(d)}\xrightarrow{\rm emp}(U^0,\ldots,U^T,G^0,\ldots,G^T,H),$$
--   $$(V^0,\ldots,V^T,M^0,\ldots,M^T)\xrightarrow{\rm str}(S^0,\ldots,S^T,W^0,\ldots,W^T),$$
--
--   and for every $\eta>0$,
--
--   $$\mathbb P\left(\|A(\widehat m-m^T)\|_{\rm op}>2(1+\sqrt\alpha)\bigl(\mathbb E[(H-G^T)^2]\bigr)^{1/2}+\eta\right)\longrightarrow0.$$
--
--   Here $G^t=g_t(U^0,\ldots,U^t)$ and $W^t=\sum_{s\le t}a_{t,s}S^s$, with the centered Gaussian–semicircular law specified by (2.4)–(2.5). Empirical convergence tests all finite-order pseudo-Lipschitz functions; strong convergence tests both normalized traces and Euclidean operator norms of every joint noncommutative polynomial. The terminal message is not fed back. The exact constant and all three conclusions are retained for arbitrary positive aspect ratio and all admissible initialization and readout laws.
--
--   Differences from the source:
--   - encoding: positive matrix dimension d tends to infinity → natural index j represents physical dimension j+1; reason: bijection with all positive dimensions; n(j) remains arbitrary
--   - encoding: self-adjoint real matrix tuples and noncommutative polynomials → real matrices are complexified for scalar complex polynomial tests; reason: all source polynomials and Euclidean operator norms are preserved
--   - encoding: the recursively specified Gaussian–semicircular limiting process → arbitrary probability/C*-space realizations satisfying precisely the state law; reason: finite Gaussian covariance and semicircular Fock realizations exist and have identical moments and faithful norms
--   - encoding: sample sizes n(d) with n(d) → ∞ → n(d) ≥ 1 for every d; reason: nondegeneracy only; at n = 0 the source's 1/n and n^{-1/2} normalizations are undefined, and n(d) → ∞ leaves only finitely many such d, which no limit statement sees
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 5, Theorem 2.9, all of (2.8), (2.9), (2.10); setup pp. 2–5

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Theorem 2.9, all of (2.8)–(2.10), submission p.5. -/
theorem state_evolution
    {Ω E B : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [CStarAlgebra B]
    (D : FiniteData Ω) (L : LimitData E B) (T : ℕ) (α : ℝ) (hT : 1 ≤ T)
    (hA : AMPAssumptions D L T α) (hL : StateLaw L T α D.a D.g)
    (h : (Fin (T+1) → ℝ) → ℝ) (hr : BoundedReadout L.ν (L.inputs T) h) :
    Empirical D.μ L.ν D.n
      (fun d ω i => append (vectorTuple D (T+1) (T+1) d ω i) (D.terminal h d ω i))
      (fun ξ => append (limitTuple D L (T+1) (T+1) ξ) (h (L.inputs T ξ))) ∧
    Strong D.μ L.τ (matrixTuple D (T+1)) (matrixLimit D L (T+1)) ∧
    TailBound D.μ
      (fun d ω => opNorm (applyA (D.A d ω) (D.terminal h d ω - D.m T d ω)))
      (2 * (1 + Real.sqrt α) * Real.sqrt (∫ ξ, (h (L.inputs T ξ)-L.G D.g T ξ)^2 ∂L.ν)) := by sorry

end FreeProbAMP.StateEvolution
