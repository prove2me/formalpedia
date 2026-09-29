-- Prove2me | Theorems.Thm_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple
-- name    : HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/c65730b1-b8a2-533f-8822-c5435da8d41c
-- title:
--   Surjectivity of a dominating finite flat model over an unramified DVR
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, with a field $K$ made an $R$-algebra and identified with its fraction field, and let $p$ be a prime with $p \neq 2$ such that $p$ is irreducible in $R$ (i.e. $p$ is a uniformiser, so $R$ is absolutely unramified of mixed characteristic $(0,p)$). Let $H$ and $H'$ be commutative rings carrying Hopf $R$-algebra structures which are finite and flat as $R$-modules and whose comultiplications are cocommutative; thus both are coordinate rings of finite flat commutative group schemes over $R$. Assume, for some $n \in \mathbb{N}$, that for every commutative $R$-algebra $T$ every element of the convolution group $\operatorname{Hom}_{R\text{-alg}}(H,T)$ satisfies $f^{p^{n}} = 1$, and likewise for $H'$; so both group schemes are killed by $p^{n}$. Assume further that $H'$ is simple in the following sense: every ideal $I \subseteq H'$ which is $R$-saturated ($c \neq 0$ and $c\,x \in I$ imply $x \in I$), on which the counit vanishes, which is stable under the antipode, and for which the image of $\Delta(x)$ in $(H'/I) \otimes_R (H'/I)$ vanishes for all $x \in I$, equals either $\bot$ or the kernel of the counit algebra map. Finally let $j \colon H \to H'$ be an $R$-bialgebra map which is injective and whose base change to $K$ is surjective. Then $j$ is surjective.
--
--   This is the case of Raynaud's uniqueness theorem for finite flat models over an absolutely unramified discrete valuation ring ($e = 1 < p-1$, $p$ odd) in which the dominating model has no proper non-trivial saturated Hopf ideal: two finite flat $p^{n}$-torsion models of the same finite commutative $K$-group scheme, one dominating the other, coincide. It feeds the general statement [`HopfAlgebra.bijective_of_bijective_baseChange_of_pow_eq_one`](thm.html#HopfAlgebra.bijective_of_bijective_baseChange_of_pow_eq_one), where the simplicity restriction is removed by dévissage.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    [Coalgebra.IsCocomm R H']
    (n : ℕ)
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ p ^ n = 1)
    (hH' : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H' →ₐ[R] T)), f ^ p ^ n = 1)
    (hsimple : ∀ I : Ideal H',
      (∀ (c : R) (x : H'), c ≠ 0 → c • x ∈ I → x ∈ I) →
      (∀ x ∈ I, Coalgebra.counit (R := R) x = 0) →
      (∀ x ∈ I, HopfAlgebra.antipode R x ∈ I) →
      (∀ x ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) = 0) →
      I = ⊥ ∨ I = RingHom.ker (Bialgebra.counitAlgHom R H'))
    (j : H →ₐc[R] H') (hj : Function.Injective j)
    (hjK : Function.Surjective ((j : H →ₐ[R] H').toLinearMap.baseChange K)) :
    Function.Surjective j := by sorry
