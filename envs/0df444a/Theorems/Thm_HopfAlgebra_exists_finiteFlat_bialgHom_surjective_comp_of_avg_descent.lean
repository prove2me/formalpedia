-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent
-- name    : HopfAlgebra.exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/2b6f2263-b0ad-55c3-92ad-bf9c2ff95241
-- title:
--   Finite flat Hopf quotient by a finite set of L-points
-- statement:
--   Let $R$ be a principal ideal domain, let $L$ be an algebraically closed field which is an $R$-algebra with $R \to L$ injective, and let $G$ be a commutative ring carrying a Hopf algebra structure over $R$ which is finite and flat as an $R$-module and whose comultiplication is cocommutative. Let $K$ be a finite set of $R$-algebra homomorphisms $G \to L$ (the $L$-points of $G$) subject to: the composite of the counit $G \to R$ with $R \to L$ lies in $K$; $K$ is closed under the convolution product (the product on $G \to L$ transported through the `WithConv` synonym); for every $k \in K$ some $k' \in K$ has underlying linear map $k \circ \mathrm{antipode}$; and, for every $g \in G$, there are $r \in R$, $r \neq 0$, and $g' \in G$ with $r \cdot \sum_{k \in K} (k \otimes \mathrm{id})(\Delta g) = 1 \otimes_R g'$ in $L \otimes_R G$. Then there exists a commutative ring $H'$ with an $R$-Hopf algebra structure, finite and flat over $R$ and cocommutative, together with an $R$-bialgebra homomorphism $\iota : H' \to G$, such that restriction along $\iota$ maps the $R$-algebra homomorphisms $G \to L$ onto those $H' \to L$, and two such $\varphi, \psi$ agree on $H'$ if and only if $\psi = k * \varphi$ for some $k \in K$, where $*$ is convolution.
--
--   In the language of group schemes: $\operatorname{Spec} H'$ is the quotient of the finite flat commutative group scheme $\operatorname{Spec} G$ over the principal ideal domain $R$ by the finite subgroup of $L$-points $K$, the averaging hypothesis supplying the descent of $K$-invariants to $R$. It is the general mechanism behind the construction of finite flat quotients used by [`HopfAlgebra.exists_finiteFlat_quotient_of_forall_fixing_smul_mem`](thm.html#HopfAlgebra.exists_finiteFlat_quotient_of_forall_fixing_smul_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {L : Type} [Field L] [Algebra R L] [IsAlgClosed L]
    (hRL : Function.Injective (algebraMap R L))
    (G : Type) [CommRing G] [HopfAlgebra R G]
    [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
    (K : Finset (G →ₐ[R] L))
    (hKone : (Algebra.ofId R L).comp (Bialgebra.counitAlgHom R G) ∈ K)
    (hKmul : ∀ k ∈ K, ∀ k' ∈ K,
      WithConv.ofConv (WithConv.toConv k * WithConv.toConv k') ∈ K)
    (hKS : ∀ k ∈ K, ∃ k' ∈ K,
      k'.toLinearMap = k.toLinearMap ∘ₗ HopfAlgebra.antipode R)
    (hdesc : ∀ g : G, ∃ (r : R) (g' : G), r ≠ 0 ∧
      r • (∑ k ∈ K, (Algebra.TensorProduct.map k (AlgHom.id R G)).comp
        (Bialgebra.comulAlgHom R G) g) = (1 : L) ⊗ₜ[R] g') :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ ι : H' →ₐc[R] G,
        Function.Surjective (fun φ : G →ₐ[R] L => φ.comp (ι : H' →ₐ[R] G)) ∧
        ∀ φ ψ : G →ₐ[R] L, φ.comp (ι : H' →ₐ[R] G) = ψ.comp (ι : H' →ₐ[R] G) ↔
          ∃ k ∈ K, ψ = WithConv.ofConv (WithConv.toConv k * WithConv.toConv φ) := by sorry
