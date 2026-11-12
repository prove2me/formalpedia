-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_positive_limiting_grams
-- name    : FreeProbAMP.StateEvolution.positive_limiting_grams
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:19.617919+00:00
-- url     : https://prove2.me/theorems/2b98d1cd-9887-4c82-8318-e8d58e685b6f
-- title:
--   Lemma 5.3 — positive limiting Gram matrices
-- statement:
--   Let $\alpha>0$, let $U^0$ have moments of every order, and let the coefficients and maps obey Assumptions 2.3–2.5 through horizon $T$. For the recursively specified Gaussian–semicircular state law, put $G^r=g_r(U^0,\ldots,U^r)$ and $W^r=\sum_{s\le r}a_{r,s}S^s$. For every $0\le t\le T$,
--
--   $$\Gamma_{G,t}=(\mathbb E[G^rG^s])_{r,s\le t}\succ0,\qquad
--   \Gamma_{W,t}=(\tau(W^rW^s))_{r,s\le t}\succ0.$$
--
--   Both inequalities mean strict positivity on every nonzero real coefficient vector. They provide limiting invertibility as a conclusion, without assuming nondegeneracy of the Gaussian or semicircular covariance matrices.
--
--   Differences from the source:
--   - encoding: the recursively specified Gaussian–semicircular limiting process → arbitrary probability/C*-space realizations satisfying precisely the state law; reason: finite Gaussian covariance and semicircular Fock realizations exist and have identical moments and faithful norms
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), pp. 28–29, Lemma 5.3 and proof

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Lemma 5.3, submission pp.28–29. -/
theorem positive_limiting_grams
    {E B : Type*} [MeasurableSpace E] [CStarAlgebra B]
    (L : LimitData E B) (T : ℕ) (α : ℝ) (a : ℕ → ℕ → ℝ) (g : ScalarMaps)
    (hα : 0 < α) (hu : AllMoments L.ν (fun ξ (_ : Fin 1) => L.U 0 ξ))
    (ha : Coefficients T a) (hr : RegularMaps T g) (hg : LastLinear T g)
    (hl : StateLaw L T α a g) :
    ∀ t, t ≤ T →
      PositiveDefinite (fun r s : Fin (t+1) => ∫ ξ, L.G g r ξ * L.G g s ξ ∂L.ν) ∧
      PositiveDefinite (fun r s : Fin (t+1) => (L.τ.value (L.W a r * L.W a s)).re) := by sorry

end FreeProbAMP.StateEvolution
