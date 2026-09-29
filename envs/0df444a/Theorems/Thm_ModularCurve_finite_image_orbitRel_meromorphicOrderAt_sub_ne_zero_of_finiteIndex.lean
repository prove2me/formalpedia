-- Prove2me | Theorems.Thm_ModularCurve_finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero_of_finiteIndex
-- name    : ModularCurve.finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/d3caa0b8-ef69-5ccb-82b3-cfdc428f6b76
-- title:
--   Finitely many Γ-orbits of zeros and poles of F-t
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index and let $F : \mathbb{H} \to \mathbb{C}$ be a function on the upper half plane, regarded near each point of $\mathbb{H}$ as a function of a complex variable by composing with the retraction `ofComplex` of $\mathbb{C}$ onto $\mathbb{H}$. Assume: for every $\tau \in \mathbb{H}$ the function $z \mapsto F(\mathrm{ofComplex}\, z)$ is meromorphic at the point $\tau$ of $\mathbb{C}$; $F$ is $\Gamma$-invariant, i.e. $F(\gamma \cdot \tau) = F(\tau)$ for all $\gamma \in \Gamma$ and all $\tau \in \mathbb{H}$. Let $t \in \mathbb{C}$ and assume further that for every $\tau \in \mathbb{H}$ the meromorphic order of $z \mapsto F(\mathrm{ofComplex}\, z) - t$ at $\tau$ is not $\top$ (that is, $F - t$ does not vanish identically near $\tau$), and that for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is a limit $L \neq t$ such that $\tau \mapsto F(\sigma \cdot \tau)$ tends to $L$ along the filter $\mathrm{atImInfty}$. Then the image in the orbit space $\Gamma \backslash \mathbb{H}$, under the quotient map for the orbit relation of the $\Gamma$-action, of the set of $\tau \in \mathbb{H}$ at which the meromorphic order of $z \mapsto F(\mathrm{ofComplex}\, z) - t$ is non-zero, is finite.
--
--   This is the finiteness of the fibre above $t$ together with the polar divisor of a meromorphic $\Gamma$-invariant function on $\mathbb{H}$ whose translates are bounded away from $t$ near the cusps — classically, finiteness of a divisor on the compact Riemann surface $\Gamma \backslash \mathbb{H}^{*}$, here stated on the upper half plane without reference to the function field. It is used in the construction of Abel-type fibre sums, where it supplies the finiteness needed to sum over the points of a fibre: it is cited by [`ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf`](thm.html#ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero_of_finiteIndex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (t : ℂ)
    (hne : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    Set.Finite (Quotient.mk (MulAction.orbitRel Γ ℍ) ''
      {τ : ℍ | meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ 0}) := by sorry
