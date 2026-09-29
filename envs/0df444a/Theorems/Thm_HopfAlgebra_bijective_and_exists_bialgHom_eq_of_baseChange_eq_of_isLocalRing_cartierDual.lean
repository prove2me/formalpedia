-- Prove2me | Theorems.Thm_HopfAlgebra_bijective_and_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual
-- name    : HopfAlgebra.bijective_and_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/21eea2f6-58ee-5b61-99b0-5a97870e32cb
-- title:
--   Fontaine's fifth step: isomorphism detected on the special fibre
-- statement:
--   Let $O$ be a discrete valuation domain, $p$ a prime number which is irreducible in $O$ (so a uniformiser), and $k$ a field equipped with an $O$-algebra structure whose structure map $O \to k$ is surjective with kernel the ideal $pO$; thus $k$ is identified with the residue field $O/pO$. Let $\mathcal R$ be a commutative ring with an $O$-bialgebra structure which is finite and free as an $O$-module, and let $H$ be a commutative ring with a cocommutative $O$-Hopf algebra structure, finite and free as an $O$-module, of $O$-rank $p^a$ for some natural number $a$, and assume that [`CartierDual k (TensorProduct O k H)`](def/HopfAlgebra_CartierDual.html#L12) — as a type, the $k$-linear dual of $k \otimes_O H$, carrying its ring structure — is a local ring. Let $\psi \colon k \otimes_O H \to k \otimes_O \mathcal R$ be a bijective homomorphism of $k$-bialgebras, and let $x \colon H \to \mathcal R$ be a homomorphism of $O$-algebras whose base change $\mathrm{id}_k \otimes x$ equals the $k$-algebra homomorphism underlying $\psi$. Then $x$ is bijective, and there is a homomorphism of $O$-bialgebras $\Phi \colon H \to \mathcal R$ whose underlying $O$-algebra homomorphism is $x$.
--
--   In scheme language: a morphism over $O$ from a finite flat commutative monoid scheme $\operatorname{Spec} \mathcal R$ to a finite flat commutative unipotent $p$-group scheme $\operatorname{Spec} H$ which becomes an isomorphism of group schemes on the special fibre is itself an isomorphism of group schemes; this is the concluding step of Fontaine's classification of finite commutative group schemes over an absolutely unramified base by finite Honda systems. The proof invokes the rigidity statement [`HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual`](thm.html#HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual), and the result is used in the construction of a $p$-divisible tower in [`Deformation.exists_pDivisibleTower_surjective_ker_eq_map_of_isLocalRing_cartierDual_zmodp`](thm.html#Deformation.exists_pDivisibleTower_surjective_ker_eq_map_of_isLocalRing_cartierDual_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_bijective_and_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w w'

theorem HopfAlgebra.bijective_and_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : O))
    (k : Type v) [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {(p : O)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra O ℛ] [Module.Finite O ℛ] [Module.Free O ℛ]
    (H : Type w') [CommRing H] [HopfAlgebra O H] [Coalgebra.IsCocomm O H]
    [Module.Finite O H] [Module.Free O H] (hrank : ∃ a : ℕ, Module.finrank O H = p ^ a)
    (hunip : IsLocalRing (CartierDual k (TensorProduct O k H)))
    (ψ : TensorProduct O k H →ₐc[k] TensorProduct O k ℛ) (hψ : Function.Bijective ψ)
    (x : H →ₐ[O] ℛ)
    (hx : Algebra.TensorProduct.map (AlgHom.id k k) x =
      (ψ : TensorProduct O k H →ₐ[k] TensorProduct O k ℛ)) :
    Function.Bijective x ∧ ∃ Φ : H →ₐc[O] ℛ, (Φ : H →ₐ[O] ℛ) = x := by sorry
