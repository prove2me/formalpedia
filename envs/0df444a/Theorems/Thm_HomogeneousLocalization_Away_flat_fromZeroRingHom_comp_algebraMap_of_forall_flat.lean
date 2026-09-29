-- Prove2me | Theorems.Thm_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
-- name    : HomogeneousLocalization.Away.flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/b1cf8472-c0a0-5b14-beb8-0c93b6a5d31e
-- title:
--   Flatness of degree-zero homogeneous localisations (A_f)₀
-- statement:
--   Let $S$ be a commutative ring and $A$ a commutative $S$-algebra equipped with an $\mathbb{N}$-grading $\mathcal{A} : \mathbb{N} \to \mathrm{Submodule}\ S\ A$ making $A$ a graded $S$-algebra, so that $A$ is the internal direct sum of the $S$-submodules $\mathcal{A}_n$ and $\mathcal{A}_m \cdot \mathcal{A}_n \subseteq \mathcal{A}_{m+n}$ with $1 \in \mathcal{A}_0$. Assume that for every $n$ the graded piece $\mathcal{A}_n$ is a flat $S$-module. Let $d$ be a natural number and $f \in \mathcal{A}_d$ a homogeneous element of degree $d$. The conclusion concerns the composite ring homomorphism from $S$ to the degree-zero homogeneous localisation of $A$ at the multiplicative set of powers of $f$, namely the structure map $S \to A$ followed by the projection $A \to \mathcal{A}_0$ onto the degree-zero part (a ring homomorphism onto $\mathcal{A}_0$ viewed as a ring) followed by the canonical map $\mathcal{A}_0 \to \mathrm{HomogeneousLocalization}\ \mathcal{A}\ (\mathrm{Submonoid.powers}\ f)$ sending $a$ to $a/1$. The assertion is that this composite is a flat ring homomorphism, i.e. that $(A_f)_0$ is flat as an $S$-module via this map.
--
--   This is the affine-chart form of the statement that $\operatorname{Proj} A \to \operatorname{Spec} S$ is flat when all graded pieces of $A$ are flat over $S$: on the standard open $D_+(f)$ the chart ring is $(A_f)_0$. It is used to obtain flatness of projective space and, more generally, flatness of the charts of Proj, feeding into [`AlgebraicGeometry.ProjSpace.flat_pi`](thm.html#AlgebraicGeometry.ProjSpace.flat_pi) and [`HomogeneousLocalization.Away.flat_quotientMk_comp_of_forall_flat_piece`](thm.html#HomogeneousLocalization.Away.flat_quotientMk_comp_of_forall_flat_piece).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open HomogeneousLocalization

theorem HomogeneousLocalization.Away.flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
    {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
    (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜]
    (hflat : ∀ n : ℕ, Module.Flat S (𝒜 n))
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) :
    ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
        ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap S A))).Flat := by sorry
