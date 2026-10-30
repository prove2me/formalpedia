-- Prove2me | Theorems.Thm_KuhnWass2019_Reformulation_piecewise_concave_convex_reformulation
-- name    : KuhnWass2019.Reformulation.piecewise_concave_convex_reformulation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T03:16:23.128603+00:00
-- url     : https://prove2.me/theorems/1bbc5a5f-24e8-4cb3-a238-6c00145da0ed
-- title:
--   Theorem 8 and Remark 1 — exact convex reformulation and both endpoints
-- statement:
--   Let $\Xi$ be convex and closed in a real finite-dimensional space with an arbitrary norm. Let $N,J\ge1$, let $\widehat\xi_i\in\Xi$, and let $P_N=N^{-1}\sum_i\delta_{\widehat\xi_i}$. Suppose each $-\ell_j$ is proper, convex and lower semicontinuous on the ambient space. Set $\ell=\max_j\ell_j$, satisfying the standing Assumption 1: measurability, upper semicontinuity and absolute integrability under $P_N$. Constituents may equal $-\infty$, and are not required to be finite anywhere in $\Xi$ individually.
--   For every $\varepsilon\ge0$ and every finite $p\ge1$, the worst-case risk equals the infimum of $\gamma\varepsilon^p+N^{-1}\sum_i s_i$ over $\gamma\ge0$, real $s_i$, and dual vectors $u_{ij},v_{ij}$ satisfying
--   $$[-\ell_j]^*(u_{ij}-v_{ij})+\sigma_\Xi(v_{ij})-u_{ij}(\widehat\xi_i)+\varphi(q)\gamma\|u_{ij}/\gamma\|_*^q\le s_i.$$
--   For $p>1$, $q=p/(p-1)$ and $\varphi(q)=(q-1)^{q-1}/q^q$; the zero-multiplier value is the closed perspective. For $p=1$, the penalty is replaced by the constraint $\|u_{ij}\|_*\le\gamma$.
--   The same goal includes Remark 1's type-infinity endpoint: the worst-case risk over the infinity-Wasserstein ball equals the infimum of $N^{-1}\sum_i s_i$ with the penalty replaced by $\varepsilon\|u_{ij}\|_*$. Both programs use the explicit convex constraints of the page. Values may be infinite and no minimizer is asserted.
--
--   Differences from the source:
--   - encoding: real finite-dimensional vector space with an arbitrary norm → finite-dimensional real normed space with its Borel sigma-algebra and continuous linear functionals as dual vectors; reason: a choice of basis identifies every such space with R^m equipped with the transported norm; the operator norm is the source dual norm
--   - encoding: extended losses, extended expectations and constrained extrema → EReal extrema and the positive-part-first extended expectation; nominal absolute integrability is a lower integral of positive plus negative parts; reason: preserves both infinities, all distributions, and the printed infinity-minus-infinity convention
--   - encoding: sample and piece indices 1 through N and J; conjugate exponents p and q; Theorem 8 and the two endpoints of Remark 1 → Fin N and Fin J with positive cardinalities; q=p/(p-1) for p>1; a conjunction of all finite orders and the infinity endpoint; reason: reindexes finite families and eliminates the uniquely determined finite conjugate exponent; the two endpoint formulas retain every displayed constraint
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen and Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2 (4 Nov 2024), p. 11, Theorem 8, equation (11), and Remark 1

import Mathlib
import Definitions.Def_KuhnWass2019_Reformulation_RegularLoss
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_KuhnWass2019_Reformulation_worstCaseRisk
import Definitions.Def_KuhnWass2019_Reformulation_finiteProgramValue
import Definitions.Def_KuhnWass2019_Reformulation_infinityWorstCaseRisk
import Definitions.Def_KuhnWass2019_Reformulation_infinityProgramValue

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

/-- Theorem 8 and Remark 1, arXiv:1908.08729v2, p. 11: the full finite-p
reformulation (including p=1) and the type-infinity endpoint. -/
theorem piecewise_concave_convex_reformulation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {N J : ℕ} (hN : 0 < N) (hJ : 0 < J)
    (Ξ : Set E) (hΞc : Convex ℝ Ξ) (hΞcl : IsClosed Ξ)
    (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ℓ : Fin J → E → EReal) (hpieces : ∀ j, ShortestGCS.MICP.IsProperClosedConvex (fun x => -ℓ j x))
    (hℓ : RegularLoss (WassersteinDRO.Duality.empiricalDistribution ξhat)
      (WassDDRO.Reduction.maxLoss ℓ))
    (ε : ℝ) (hε : 0 ≤ ε) :
    (∀ p : ℝ, 1 ≤ p →
      worstCaseRisk ε p Ξ (WassersteinDRO.Duality.empiricalDistribution ξhat)
        (WassDDRO.Reduction.maxLoss ℓ) = finiteProgramValue ε p Ξ ξhat ℓ) ∧
    infinityWorstCaseRisk ε Ξ (WassersteinDRO.Duality.empiricalDistribution ξhat)
      (WassDDRO.Reduction.maxLoss ℓ) = infinityProgramValue ε Ξ ξhat ℓ := by sorry

end KuhnWass2019.Reformulation
