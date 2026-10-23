-- Prove2me | Theorems.Thm_JHolomorphic_tendstoCInftyLocOn_tangent
-- name    : JHolomorphic.tendstoCInftyLocOn_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T22:25:40.205003+00:00
-- url     : https://prove2.me/theorems/5184b336-2ee6-43c5-9092-12940144eeb1
-- title:
--   $C^\infty_{\mathrm{loc}}$ convergence of almost complex structures passes to their tangent structures
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $O\subseteq E$ open, and let $J_\nu$, $J$ be smooth almost complex structures on $O$ with $J_\nu\to J$ in $C^\infty_{\mathrm{loc}}$ on $O$. Then the tangent structures
--   $$J_\nu^T(x,y)(a,b)=\bigl(J_\nu(x)a,\ J_\nu(x)b+DJ_\nu(x)[y]\,a\bigr)$$
--   converge to $J^T$ in $C^\infty_{\mathrm{loc}}$ on $O\times E$: for every compact $K\subseteq O\times E$ and every $m$, $D^mJ_\nu^T\to D^mJ^T$ uniformly on $K$.
--
--   **Formalization Note** The tangent structures are written inline as `fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) + (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E))`, and the same with `Jν ν` in place of `J`. The hypotheses are `IsAlmostComplexOn J O`, `∀ ν, IsAlmostComplexOn (Jν ν) O` and `TendstoCInftyLocOn Jν J O`; the conclusion is `TendstoCInftyLocOn` of the tangent structures on `O ×ˢ Set.univ`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, proof of Theorem 2.22

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

/-- `C^∞_loc` convergence passes to tangent structures: if `J_ν → J` in `C^∞_loc` on the open set
`O ⊆ E`, all of them smooth almost complex structures on `O`, then the tangent structures
`J_ν^T(x, y)(a, b) = (J_ν(x) a, J_ν(x) b + DJ_ν(x)[y] a)` converge to `J^T` in `C^∞_loc` on
`O × E`. -/
theorem tendstoCInftyLocOn_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E)
    (Jν : ℕ → E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O)
    (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O) (hconv : TendstoCInftyLocOn Jν J O) :
    TendstoCInftyLocOn
      (fun ν (x : E × E) => ((Jν ν x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((Jν ν x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ (Jν ν) x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      (O ×ˢ Set.univ) := by
  sorry

end JHolomorphic
