-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_smooth_extra_half_step
-- name    : FreeProbAMP.StateEvolution.smooth_extra_half_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:54.988253+00:00
-- url     : https://prove2.me/theorems/25dd7ae4-c844-4553-b9f5-905bd1c2b320
-- title:
--   Lemma 7.3 — strong limit of a smooth extra half-step
-- statement:
--   Run the AMP trajectory through time $T-1$, for fixed $T\ge1$. Let $k:\mathbb R^{T+1}\to\mathbb R$ be $C^1$ with its value and first derivatives pseudo-Lipschitz of finite order; no last-coordinate linearity or slope condition is imposed on $k$. Define $\widehat z_i=k(u_i^0,\ldots,u_i^T)$, $K=k(U^0,\ldots,U^T)$, $d_{k,r}$ and $c_{k,r}$ as the empirical and limiting partial-derivative means, and $\widehat V$ as in (7.3). There exists a centered semicircular extension $\widehat S$, jointly semicircular with $S^0,\ldots,S^{T-1}$, satisfying
--
--   $$\tau(\widehat S^2)=\mathbb E[K^2],\qquad
--   \tau(\widehat SS^s)=\mathbb E[KG^s]\quad(0\le s<T),$$
--   $$(V^0,\ldots,V^{T-1},\widehat V,M^0,\ldots,M^{T-1})\xrightarrow{\rm str}
--   (S^0,\ldots,S^{T-1},\widehat S,W^0,\ldots,W^{T-1}).$$
--
--   For the same extension, the consequence also holds:
--
--   $$A\widehat z\xrightarrow{\rm str}\widehat S+\alpha\sum_{r=1}^T c_{k,r}W^{r-1}.$$
--
--   This identifies the full extra-half-step limit and its covariances. Existence of the extension is part of the conclusion, rather than a hypothesis supplied to obtain convergence.
--
--   Differences from the source:
--   - encoding: positive matrix dimension d tends to infinity → natural index j represents physical dimension j+1; reason: bijection with all positive dimensions; n(j) remains arbitrary
--   - encoding: self-adjoint real matrix tuples and noncommutative polynomials → real matrices are complexified for scalar complex polynomial tests; reason: all source polynomials and Euclidean operator norms are preserved
--   - encoding: the recursively specified Gaussian–semicircular limiting process → arbitrary probability/C*-space realizations satisfying precisely the state law; reason: finite Gaussian covariance and semicircular Fock realizations exist and have identical moments and faithful norms
--   - encoding: adjoin semicircular variables to the limiting family → existence in an isometric trace-preserving C*-extension; reason: the original ambient algebra need not contain a new independent semicircular direction; no source law is changed
--   - encoding: sample sizes n(d) with n(d) → ∞ → n(d) ≥ 1 for every d; reason: nondegeneracy only; at n = 0 the source's 1/n and n^{-1/2} normalizations are undefined, and n(d) → ∞ leaves only finitely many such d, which no limit statement sees
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 38, Lemma 7.3, (7.3)–(7.4) and preceding setup

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_Terminal

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Lemma 7.3, submission p.38, including the consequence (7.4).
The extra map k need not satisfy Assumption 2.5. -/
theorem smooth_extra_half_step
    {Ω E B : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [CStarAlgebra B]
    (D : FiniteData Ω) (L : LimitData E B) (T : ℕ) (α : ℝ) (hT : 1 ≤ T)
    (hA : AMPAssumptions D L (T-1) α) (hL : StateLaw L (T-1) α D.a D.g)
    (k : (Fin (T+1) → ℝ) → ℝ) (hk : SmoothPL k) :
    ∃ C : TraceExtension B L.τ, ∃ s : C.carrier,
      JointSemicircular C.trace (Sum.elim (fun j : Fin T => C.embed (L.S j)) (fun _ : Unit => s)) ∧
      C.trace.value (s*s) = ((∫ ξ, k (L.inputs T ξ)^2 ∂L.ν) : ℂ) ∧
      (∀ j : Fin T, C.trace.value (s*C.embed (L.S j)) =
        ((∫ ξ, k (L.inputs T ξ)*L.G D.g j ξ ∂L.ν) : ℂ)) ∧
      Strong D.μ C.trace
        (fun d ω => Sum.elim (Sum.elim (fun j : Fin T => D.V j d ω)
          (fun _ : Unit => extraV D T k d ω)) (fun j : Fin T => D.M j d ω))
        (Sum.elim (Sum.elim (fun j : Fin T => C.embed (L.S j)) (fun _ : Unit => s))
          (fun j : Fin T => C.embed (L.W D.a j))) ∧
      Strong D.μ C.trace
        (fun d ω (_ : Unit) => applyA (D.A d ω) (extraMessage D T k d ω))
        (fun _ : Unit => s + ∑ r : Fin T,
          (α * extraCovDerivative L T k r : ℂ) • C.embed (L.W D.a r)) := by sorry

end FreeProbAMP.StateEvolution
