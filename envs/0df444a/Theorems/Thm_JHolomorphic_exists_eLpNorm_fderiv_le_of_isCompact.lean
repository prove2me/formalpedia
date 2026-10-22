-- Prove2me | Theorems.Thm_JHolomorphic_exists_eLpNorm_fderiv_le_of_isCompact
-- name    : JHolomorphic.exists_eLpNorm_fderiv_le_of_isCompact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T00:28:09.538698+00:00
-- url     : https://prove2.me/theorems/ef750464-48a1-4d42-b71f-865462df5d72
-- title:
--   A uniform planar $L^p$ estimate for $\partial_s+J_0\,\partial_t$ over a compact family of complex structures
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $p>1$, and let $S$ be a compact set of linear maps $J_0:E\to E$ with $J_0^2=-1$ for every $J_0\in S$. Then there is $C\in\mathbb R$ such that for every $J_0\in S$ and every compactly supported $C^1$ map $g:\mathbb C\to E$,
--   $$\|\partial_sg\|_{L^p}+\|\partial_tg\|_{L^p}\le C\,\|\partial_sg+J_0\,\partial_tg\|_{L^p}.$$
--   Here $z=s+it$, $\partial_sg=Dg(z)1$ and $\partial_tg=Dg(z)i$. This gives one constant for the frozen-coefficient estimate along a whole compact family of complex structures, as needed for uniform estimates on sequences of pseudoholomorphic maps.
--
--   **Formalization Note** `S : Set (E →L[ℝ] E)` is `IsCompact` and every `J₀ ∈ S` satisfies `J₀.comp J₀ = -ContinuousLinearMap.id ℝ E`; `g` satisfies `ContDiff ℝ 1 g` and `HasCompactSupport g`; the norms are `eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume` etc., and the constant enters as `ENNReal.ofReal C`.
-- source:
--   Frozen-coefficient L^p estimates for the Cauchy-Riemann operator; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.Compactness.Compact

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- The planar `L^p` estimate for `∂ₛ + J₀ ∂ₜ` holds with one constant for all `J₀` in a compact
set `S` of complex structures on `E` (`J₀² = -1`): for `1 < p` there is `C` such that
`‖∂ₛg‖_p + ‖∂ₜg‖_p ≤ C ‖∂ₛg + J₀ ∂ₜg‖_p` for every `J₀ ∈ S` and every compactly supported `C¹`
map `g : ℂ → E`. -/
theorem exists_eLpNorm_fderiv_le_of_isCompact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (S : Set (E →L[ℝ] E))
    (hS : IsCompact S) (hSJ : ∀ J₀ ∈ S, J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, ∀ J₀ ∈ S, ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume := by
  sorry

end JHolomorphic
