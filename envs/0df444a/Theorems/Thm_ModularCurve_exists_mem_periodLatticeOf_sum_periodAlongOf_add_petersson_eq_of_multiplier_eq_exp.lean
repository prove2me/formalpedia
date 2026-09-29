-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp
-- name    : ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/8bfe68f4-ddec-500c-9953-a7818bea4733
-- title:
--   Divisor periods plus Petersson pairing lie in the period lattice
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index with $-1\in\Gamma$, let $F:\mathfrak H\to\mathbb C$ be a function and $k$ a cusp form of weight $2$ for $\Gamma$. Assume: (i) the function $z\mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at every point of the upper half-plane; (ii) for all $\gamma\in\Gamma$ and $\tau\in\mathfrak H$, $F(\gamma\cdot\tau)=\exp\bigl(2\pi i\,\mathrm{Re}(\mathrm{periodOf}\,\Gamma\,\gamma\,k)\bigr)F(\tau)$, where $\mathrm{periodOf}\,\Gamma\,\gamma$ is the linear functional on weight-$2$ cusp forms given by integration along the straight segment from $i$ to $\gamma\cdot i$; (iii) for every $\sigma\in\mathrm{SL}_2(\mathbb Z)$ the function $\tau\mapsto F(\sigma\cdot\tau)$ tends, as $\mathrm{Im}\,\tau\to\infty$, to a non-zero limit. Let $S\subseteq\mathfrak H$ be a finite set and $n:\mathfrak H\to\mathbb Z$ with: the meromorphic order of $F$ at each $s\in S$ equals $n(s)$; distinct points of $S$ are $\Gamma$-inequivalent; and every $\tau$ at which $F$ has non-zero order is $\Gamma$-equivalent to a point of $S$. Then there is a functional $\Lambda$ in the $\mathbb Z$-span of the range of $\mathrm{periodOf}\,\Gamma$ inside the $\mathbb C$-dual of $\mathrm{CuspForm}\,\Gamma\,2$ such that for every weight-$2$ cusp form $g$ for $\Gamma$,
--   $$\sum_{s\in S}\frac{2n(s)}{\#\mathrm{Stab}_\Gamma(s)}\,\mathrm{periodAlongOf}\,\Gamma\,i\,s\,(g)\;+\;i\int_{\mathcal F_\Gamma}\mathrm{petersson}\,2\,k\,g\,(\tau)\;+\;\Lambda(g)=0,$$
--   where $\mathrm{periodAlongOf}\,\Gamma\,i\,s$ is integration along the segment from $i$ to $s$ and $\mathcal F_\Gamma=\bigcup_{q\in\mathrm{SL}_2(\mathbb Z)/\Gamma}q_{\mathrm{out}}^{-1}\cdot\mathcal D$ is the coset-indexed union of translates of the standard fundamental domain.
--
--   This is the reciprocity relation on the modular curve $X_\Gamma$ obtained by applying Stokes' theorem on a cut fundamental domain to $\mathrm{d}\log$ of the $\Gamma$-invariant untwisting of $F$ wedged with $g\,\mathrm{d}z$: the local contributions at the zeros and poles of $F$ give the divisor periods, the area term gives the Petersson pairing against $k$, and the side identifications contribute an integral combination of periods. It is stated for an arbitrary finite-index $\Gamma$ containing $-1$ and is used by [`ModularCurve.exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp`](thm.html#ModularCurve.exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

set_option autoImplicit false

theorem ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ s ∈ S, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (s : ℂ) = (n s : WithTop ℤ))
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hcov : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
      ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ) :
    ∃ Λ ∈ ModularCurve.periodLatticeOf Γ,
      ∀ g : CuspForm (Γ) 2,
        (∑ s ∈ S, (2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer (Γ) s) : ℂ)) *
              ModularCurve.periodAlongOf Γ UpperHalfPlane.I s g) +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (Γ), UpperHalfPlane.petersson 2 k g τ) +
          Λ g = 0 := by sorry
