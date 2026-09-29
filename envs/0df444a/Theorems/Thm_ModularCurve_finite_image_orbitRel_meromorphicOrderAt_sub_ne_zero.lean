-- Prove2me | Theorems.Thm_ModularCurve_finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero
-- name    : ModularCurve.finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/53ac12d8-2024-54cc-b84f-5b71ca23fff8
-- title:
--   Finitely many Γ₀(N)-orbits of zeros and poles of F-t
-- statement:
--   Let $N$ be a positive natural number and let $F:\mathbb{H}\to\mathbb{C}$ be a function on the upper half-plane. Assume: (i) for every $\tau\in\mathbb{H}$ the function $z\mapsto F(\mathrm{ofComplex}\,z)$ on $\mathbb{C}$, obtained from $F$ by the canonical extension `ofComplex` of a complex variable to $\mathbb{H}$, is meromorphic at the point $\tau$; (ii) $F$ is invariant under the congruence subgroup $\Gamma_0(N)$, i.e. $F(\gamma\cdot\tau)=F(\tau)$ for all $\gamma\in\Gamma_0(N)$ and all $\tau\in\mathbb{H}$. Let $t\in\mathbb{C}$ and assume further: (iii) at no point $\tau\in\mathbb{H}$ does $z\mapsto F(\mathrm{ofComplex}\,z)-t$ have meromorphic order $\top$, that is, $F-t$ vanishes identically near no point; (iv) for every $\sigma\in\mathrm{SL}_2(\mathbb{Z})$ there is a limit $L\neq t$ such that $F(\sigma\cdot\tau)\to L$ along the filter $\mathrm{atImInfty}$ of $\mathrm{Im}\,\tau\to\infty$. The conclusion is that the set of $\tau\in\mathbb{H}$ at which the meromorphic order of $z\mapsto F(\mathrm{ofComplex}\,z)-t$ is nonzero — the zeros of $F-t$ together with the poles of $F$ — has finite image under the quotient map onto the orbit space of the $\Gamma_0(N)$-action on $\mathbb{H}$.
--
--   This is the standard finiteness statement for the fibre of a $\Gamma_0(N)$-invariant meromorphic function over a value $t$ not attained at any cusp: the divisor of $F-t$ on the modular curve $\Gamma_0(N)\backslash\mathbb{H}$ is supported on finitely many orbits. It is used in the construction of Abel-type fibre sums, namely by [`ModularCurve.eventually_abelFibreSum_sub_mem_periodLattice`](thm.html#ModularCurve.eventually_abelFibreSum_sub_mem_periodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero
    {N : ℕ} [NeZero N] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (t : ℂ)
    (hne : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    Set.Finite (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ) ''
      {τ : ℍ | meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ 0}) := by sorry
