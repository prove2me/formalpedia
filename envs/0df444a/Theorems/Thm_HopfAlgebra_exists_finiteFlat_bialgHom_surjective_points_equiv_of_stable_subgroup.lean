-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup
-- name    : HopfAlgebra.exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/6a7a9eae-eab4-512e-9af2-cf6c2b20fb16
-- title:
--   Schematic closure of a Galois-stable subgroup of points
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K$ of characteristic $0$, and let $L$ be an algebraically closed field that is an algebraic extension of $K$, compatibly an $R$-algebra. Let $G$ be a commutative ring equipped with a Hopf $R$-algebra structure which is finite and flat as an $R$-module and whose comultiplication is cocommutative. Write `WithConv (G →ₐ[R] L)` for the set of $R$-algebra maps $G \to L$ with its convolution monoid structure, `ofConv` being the underlying algebra map, and let $N$ be a submonoid of it which is stable under the Galois action in the following relational sense: for every $K$-algebra automorphism $\sigma$ of $L$, every $f \in N$ and every $f'$ with $f'(x) = \sigma(f(x))$ for all $x \in G$, one has $f' \in N$. The conclusion asserts the existence of a commutative ring $H$ with a Hopf $R$-algebra structure, finite and flat as an $R$-module and cocommutative, together with a surjective $R$-bialgebra map $\pi \colon G \to H$, such that: composition with $\pi$ is injective on $R$-algebra maps $H \to L$; composition with $\pi$ carries the convolution product of any $h, h' \colon H \to L$ to the convolution product of $h \circ \pi$ and $h' \circ \pi$; an $R$-algebra map $f \colon G \to L$ lies in $N$ if and only if $f = h \circ \pi$ for some $R$-algebra map $h \colon H \to L$; and $\operatorname{rank}_R H = |N|$ (the cardinality of $N$ as a natural number). Note that $N$ is only assumed to be a submonoid, not a subgroup.
--
--   This is the statement that the schematic closure in a finite flat commutative group scheme $\operatorname{Spec} G$ over a principal ideal domain of a Galois-stable subgroup $N$ of its $L$-points is again a finite flat commutative closed subgroup scheme $\operatorname{Spec} H$, with $L$-points exactly $N$ and with rank over the base equal to the order of $N$. It is used in the construction of the finite part and toric quotient of the $p$-divisible group attached to the Néron model at $p$ of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type} [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    {L : Type} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosed L] [Algebra.IsAlgebraic K L]
    (G : Type) [CommRing G] [HopfAlgebra R G] [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
    (N : Submonoid (WithConv (G →ₐ[R] L)))
    (hN : ∀ (σ : L ≃ₐ[K] L), ∀ f ∈ N, ∀ f' : WithConv (G →ₐ[R] L), (∀ x : G, f'.ofConv x = σ (f.ofConv x)) → f' ∈ N) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ π : G →ₐc[R] H, Function.Surjective π ∧

        (∀ h h' : H →ₐ[R] L, h.comp (π : G →ₐ[R] H) = h'.comp (π : G →ₐ[R] H) → h = h') ∧
        (∀ h h' : WithConv (H →ₐ[R] L),
          WithConv.toConv ((h * h').ofConv.comp (π : G →ₐ[R] H)) =
            WithConv.toConv (h.ofConv.comp (π : G →ₐ[R] H)) * WithConv.toConv (h'.ofConv.comp (π : G →ₐ[R] H))) ∧
        (∀ f : WithConv (G →ₐ[R] L), f ∈ N ↔ ∃ h : H →ₐ[R] L, h.comp (π : G →ₐ[R] H) = f.ofConv) ∧

        Module.finrank R H = Nat.card ↥N := by sorry
