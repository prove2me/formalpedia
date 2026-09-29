-- Prove2me | Theorems.Thm_ModularCurve_exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex
-- name    : ModularCurve.exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/1b2ae66d-dda8-5bcf-b259-ceb536bbf924
-- title:
--   Finitely many Γ-orbits of zeros and poles of a multiplier-automorphic function
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$, let $F\colon\mathbb{H}\to\mathbb{C}$ be a function on the upper half-plane, and let $k$ be a cusp form of weight $2$ for $\Gamma$. Assume: (i) for every $\tau\in\mathbb{H}$ the function $z\mapsto F(\mathrm{ofComplex}\,z)$ on $\mathbb{C}$ is meromorphic at $\tau$; (ii) for every $\gamma\in\Gamma$ and every $\tau\in\mathbb{H}$ one has $F(\gamma\cdot\tau)=\exp\bigl(2\pi i\,\operatorname{Re}(\mathrm{periodOf}\,\Gamma\,\gamma)(k)\bigr)\,F(\tau)$, where $(\mathrm{periodOf}\,\Gamma\,\gamma)$ is the linear functional on weight-$2$ cusp forms obtained by integrating, over $t\in[0,1]$, the integrand `periodIntegrandOf` attached to the pair of points $i$ and $\gamma\cdot i$, i.e. the period of the form along a path from $i$ to $\gamma\cdot i$; (iii) for every $\sigma\in\mathrm{SL}_2(\mathbb{Z})$ there is a nonzero $L\in\mathbb{C}$ with $F(\sigma\cdot\tau)\to L$ as $\operatorname{Im}\tau\to\infty$. Then there is a finite set $S\subset\mathbb{H}$ whose elements are pairwise $\Gamma$-inequivalent (any $s,t\in S$ lying in the same $\Gamma$-orbit are equal) such that every $\tau\in\mathbb{H}$ at which the meromorphic order of $z\mapsto F(\mathrm{ofComplex}\,z)$ is nonzero lies in the $\Gamma$-orbit of some $s\in S$.
--
--   This is the finiteness statement that the zeros and poles of a meromorphic function on $\mathbb{H}$ transforming under $\Gamma$ by a constant multiplier, and with finite nonzero limits at all cusps, fall into finitely many $\Gamma$-orbits, with a chosen set of orbit representatives; it reflects the compactness of the modular curve attached to a finite-index $\Gamma$. It is used in the construction of chains of points along which the periods `periodAlongOf` of a weight-$2$ cusp form combine with Petersson-type terms to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

set_option autoImplicit false

theorem ModularCurve.exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ S : Finset ℍ,
      (∀ s ∈ S, ∀ t ∈ S,
        (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t) ∧
      ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
        ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ := by sorry
