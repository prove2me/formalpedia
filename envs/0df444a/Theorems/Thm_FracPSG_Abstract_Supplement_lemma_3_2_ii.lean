-- Prove2me | Theorems.Thm_FracPSG_Abstract_Supplement_lemma_3_2_ii
-- name    : FracPSG.Abstract.Supplement.lemma_3_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:57:32.348095+00:00
-- url     : https://prove2.me/theorems/50f9a197-99fe-4912-8121-91e8bd603fc3
-- title:
--   Lemma 3.2(ii) — quotient rule (12) for $\partial_L(f/g+\iota_S)$; stationary $\Leftrightarrow$ lifted stationary
-- statement:
--   Let $\mathcal H$ be a finite-dimensional real Hilbert space, $f:\mathcal H\to(-\infty,+\infty]$ proper and lower semicontinuous, $g:\mathcal H\to\mathbb R$ lower semicontinuous, and $S\subseteq\mathcal H$ nonempty and closed (not necessarily convex). Let $C$ be a nonempty closed set with $C\cap S\neq\varnothing$, let $\bar x\in C\cap S$, and suppose $g(\bar x)>0$ and $f=f_1+\iota_C$, where one of the following holds:
--
--   1. (a) $f_1$ is Lipschitz continuous around $\bar x$ and $\bar x\in\operatorname{int}(C\cap S)$;
--   2. (b) $f_1$ is Lipschitz continuous around $\bar x$, $f_1$ and $C\cap S$ are regular at $\bar x$, and $g$ is positive around $\bar x$;
--   3. (c) $f_1$ is strictly differentiable at $\bar x$ and $g$ is positive around $\bar x$.
--
--   If $g$ is strictly differentiable at $\bar x$, then
--   $$\partial_L\Big(\frac fg+\iota_S\Big)(\bar x)=\frac{g(\bar x)\,\partial_L(f+\iota_S)(\bar x)-f(\bar x)\nabla g(\bar x)}{g(\bar x)^2},\tag{12}$$
--   and $\bar x$ is a stationary point of $\min_{x\in S}f/g$ (that is, $0\in\partial_L(f/g+\iota_S)(\bar x)$) if and only if it is a lifted stationary point (that is, $0\in g(\bar x)\partial_L(f+\iota_S)(\bar x)-f(\bar x)\partial_L g(\bar x)$).
--
--   The formula expresses the subdifferential of the quotient through that of the numerator. Theorem 5.5 uses it to compute $\partial_L h$ of its merit function along the iterates, and Corollary 4.6 uses the equivalence to upgrade lifted stationarity of limit points to stationarity.
--
--   **Formalization Note** The right side of (12) is the image of $\partial_L(f+\iota_S)(\bar x)$ under $u\mapsto(g(\bar x)u-f(\bar x)\nabla g(\bar x))/g(\bar x)^2$. "Around $\bar x$" means on a neighbourhood of $\bar x$; Lipschitz continuity and strict differentiability of the extended-real $f_1$ include its finiteness there. Strict differentiability of $g$ is `HasStrictFDerivAt`, and $\nabla g(\bar x)$ is `gradient g x̄`.
--
--   Differences from the source:
--   - encoding: g: H → (−∞, +∞] proper lower semicontinuous → g : H → ℝ lower semicontinuous; reason: g is strictly differentiable at x̄, hence finite on a neighbourhood of x̄; both sides of (12) and both stationarity notions depend only on the values of f and g near x̄, so any extended-real g of the lemma agrees near x̄ with a real-valued one
--   - encoding: the set (g(x̄)∂_L(f + ι_S)(x̄) − f(x̄)∇g(x̄))/g(x̄)² → the image of ∂_L(f + ι_S)(x̄) under u ↦ (g(x̄)u − f(x̄)∇g(x̄))/g(x̄)², with f(x̄) read as a real number; reason: f(x̄) = f₁(x̄) is finite because f₁ is finite near x̄ in each of (a), (b), (c)
--   - encoding: g strictly differentiable at x̄ with gradient ∇g(x̄) → g has a strict Fréchet derivative at x̄ and ∇g(x̄) is Mathlib gradient g x̄; reason: a strict derivative is a derivative, so the gradient is its Riesz representative
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 7, Lemma 3.2(ii), eq. (12)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracPSG_Subseq_Basic
import Definitions.Def_FracPSG_Abstract_Supplement_Stationary

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Abstract.Supplement

open NonconvexSplitting.Shared FracPSG.Subseq

/-- Lemma 3.2(ii) (Boţ–Dao–Li, arXiv:2003.04124v2, p. 7). Let `f` be proper and lower
semicontinuous, `g` lower semicontinuous, `S` and `C` nonempty closed sets with `C ∩ S ≠ ∅`,
`xbar ∈ C ∩ S`, `g(xbar) > 0` and `f = f₁ + ι_C`, where (a) `f₁` is Lipschitz around `xbar` and
`xbar ∈ int(C ∩ S)`, or (b) `f₁` is Lipschitz around `xbar`, `f₁` and `C ∩ S` are regular at `xbar`
and `g > 0` around `xbar`, or (c) `f₁` is strictly differentiable at `xbar` and `g > 0` around
`xbar`. If `g` is strictly differentiable at `xbar`, then (12)
`∂_L(f/g + ι_S)(xbar) = (g(xbar) ∂_L(f + ι_S)(xbar) − f(xbar) ∇g(xbar)) / g(xbar)²`,
and `xbar` is a stationary point of (P) iff it is a lifted stationary point of (P). -/
theorem lemma_3_2_ii {N : ℕ} {S C : Set (EuclideanSpace ℝ (Fin N))}
    {f f₁ : EuclideanSpace ℝ (Fin N) → EReal} {g : EuclideanSpace ℝ (Fin N) → ℝ}
    {xbar : EuclideanSpace ℝ (Fin N)}
    (hf : IsProperFn f) (hflsc : LowerSemicontinuous f) (hglsc : LowerSemicontinuous g)
    (hS : IsClosed S) (hSne : S.Nonempty) (hC : IsClosed C) (hCne : C.Nonempty)
    (hCS : (C ∩ S).Nonempty) (hxC : xbar ∈ C) (hxS : xbar ∈ S) (hgx : 0 < g xbar)
    (hfeq : f = addInd f₁ C)
    (hcase : (IsLipschitzAround f₁ xbar ∧ xbar ∈ interior (C ∩ S)) ∨
      (IsLipschitzAround f₁ xbar ∧ IsRegularAt f₁ xbar ∧ IsSetRegularAt (C ∩ S) xbar ∧
        ∀ᶠ y in 𝓝 xbar, 0 < g y) ∨
      (IsStrictlyDiffAt f₁ xbar ∧ ∀ᶠ y in 𝓝 xbar, 0 < g y))
    (hgdiff : ∃ L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ, HasStrictFDerivAt g L xbar) :
    LimitingSubdiff (addInd (quotient f g) S) xbar =
      (fun u => (g xbar ^ 2)⁻¹ • (g xbar • u - (f xbar).toReal • gradient g xbar)) ''
        LimitingSubdiff (addInd f S) xbar ∧
    (IsStationary f g S xbar ↔ IsLiftedStationary f g S xbar) := by sorry

end FracPSG.Abstract.Supplement
