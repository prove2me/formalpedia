-- Prove2me | Theorems.Thm_HopfAlgebra_exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed
-- name    : HopfAlgebra.exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/5e378287-b519-5874-87a2-d0d36e1f524d
-- title:
--   Restriction of Ω-points to a Hopf kernel
-- statement:
--   Let $R$ be a commutative domain and $\Omega$ an algebraically closed field which is an $R$-algebra with injective structure map $R \to \Omega$. Let $H$, $B_1$, $B_0$ be commutative Hopf $R$-algebras that are finite free as $R$-modules and cocommutative as coalgebras, and let $\pi_1 : H \to B_1$ and $\rho : B_1 \to B_0$ be surjective morphisms of $R$-bialgebras, with $\mathrm{hopfKer}\,\rho$ — the subalgebra of $B_1$ on which $(\mathrm{id}_{B_1} \otimes \rho) \circ \Delta_{B_1}$ agrees with $b \mapsto b \otimes 1$ — finite and free over $R$. Let $N \le N'$ be submonoids of the convolution monoid $\mathrm{WithConv}(H \to_{\mathrm{alg}} \Omega)$ such that an $R$-algebra map $f : H \to \Omega$ lies in $N'$ exactly when it factors through $\pi_1$, and lies in $N$ exactly when it factors through $\rho \circ \pi_1$. Then there is a map $r$ from $\mathrm{WithConv}(H \to_{\mathrm{alg}} \Omega)$ to $\mathrm{WithConv}(\mathrm{hopfKer}\,\rho \to_{\mathrm{alg}} \Omega)$ such that, for $f \in N'$ and any $g : B_1 \to \Omega$ with $g \circ \pi_1 = f$, $r(f)$ is the restriction of $g$ along the inclusion of $\mathrm{hopfKer}\,\rho$; moreover $r(ff') = r(f)r(f')$ for $f, f' \in N'$; for $f \in N'$ one has $r(f) = 1$ iff $f \in N$; and every point of $\mathrm{hopfKer}\,\rho$ with values in $\Omega$ is $r(f)$ for some $f \in N'$. No property of $r$ outside $N'$ is asserted.
--
--   This is the exactness on $\Omega$-points of the sequence attached to a chain of Hopf quotients $H \twoheadrightarrow B_1 \twoheadrightarrow B_0$: restriction to the coordinate ring of the quotient group is multiplicative on the points of the middle subgroup, has exactly the points of the smaller subgroup as kernel, and is surjective. It is used in the analysis of towers of Hopf quotients for $p$-divisible groups over rings of integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed
    (R : Type) [CommRing R] [IsDomain R] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (hR : Function.Injective (algebraMap R Ω))
    {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    {B₁ B₀ : Type} [CommRing B₁] [HopfAlgebra R B₁] [Module.Finite R B₁] [Module.Free R B₁] [Coalgebra.IsCocomm R B₁]
    [CommRing B₀] [HopfAlgebra R B₀] [Module.Finite R B₀] [Module.Free R B₀] [Coalgebra.IsCocomm R B₀]
    (π₁ : H →ₐc[R] B₁) (hπ₁ : Function.Surjective π₁) (ρ : B₁ →ₐc[R] B₀) (hρ : Function.Surjective ρ)
    [Module.Finite R ↥(HopfAlgebra.hopfKer ρ)] [Module.Free R ↥(HopfAlgebra.hopfKer ρ)]
    (N N' : Submonoid (WithConv (H →ₐ[R] Ω))) (hNN' : N ≤ N')
    (hpts₁ : ∀ f : H →ₐ[R] Ω,
      (∃ g : B₁ →ₐ[R] Ω, g.comp (π₁ : H →ₐ[R] B₁) = f) ↔ WithConv.toConv f ∈ N')
    (hpts₀ : ∀ f : H →ₐ[R] Ω,
      (∃ g : B₀ →ₐ[R] Ω, g.comp ((ρ.comp π₁ : H →ₐc[R] B₀) : H →ₐ[R] B₀) = f) ↔ WithConv.toConv f ∈ N) :
    ∃ r : WithConv (H →ₐ[R] Ω) → WithConv (↥(HopfAlgebra.hopfKer ρ) →ₐ[R] Ω),
      (∀ f ∈ N', ∀ g : B₁ →ₐ[R] Ω, g.comp (π₁ : H →ₐ[R] B₁) = f.ofConv →
        (r f).ofConv = g.comp (HopfAlgebra.hopfKer ρ).val) ∧
      (∀ f ∈ N', ∀ f' ∈ N', r (f * f') = r f * r f') ∧
      (∀ f ∈ N', (r f = 1 ↔ f ∈ N)) ∧
      (∀ ν : WithConv (↥(HopfAlgebra.hopfKer ρ) →ₐ[R] Ω), ∃ f ∈ N', r f = ν) := by sorry
