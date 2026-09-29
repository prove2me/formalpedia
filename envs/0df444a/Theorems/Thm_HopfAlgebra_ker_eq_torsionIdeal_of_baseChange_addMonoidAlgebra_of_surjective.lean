-- Prove2me | Theorems.Thm_HopfAlgebra_ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective
-- name    : HopfAlgebra.ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/6ff3e139-1789-540b-8407-b590eb23507d
-- title:
--   Descent of p^v-torsion kernels along a faithfully flat trivialisation
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative domain and let $A$ be a commutative $R$-algebra which is faithfully flat as an $R$-module. Let $C$ and $C'$ be commutative rings carrying cocommutative Hopf algebra structures over $R$ and free and finite as $R$-modules. Let $\Lambda$ and $\Lambda'$ be finite abelian groups, and suppose given $A$-bialgebra isomorphisms $e : A \otimes_R C \simeq A[\Lambda]$ and $e' : A \otimes_R C' \simeq A[\Lambda']$ onto the additive monoid algebras. Let $v$ be a natural number and let $f : \Lambda' \to \Lambda$ be a surjective group homomorphism whose kernel consists exactly of the elements $p^v y$ with $y \in \Lambda'$. Let $t : C' \to C$ be a surjective $R$-bialgebra homomorphism which, after base change, agrees under the two trivialisations with the bialgebra map $A[\Lambda'] \to A[\Lambda]$ induced by $f$ on the indexing groups: for every $z \in A \otimes_R C'$ one has $e((\mathrm{id}_A \otimes t)(z)) = (\mathrm{mapDomain}\,f)(e'(z))$. The conclusion is that the kernel of $t$ as a ring homomorphism equals [`PDivisibleGroup.Hopf.torsionIdeal R C' (p ^ v)`](def/PDivisibleGroup_Basic.html#L157), that is, the image of the augmentation ideal $\ker(\varepsilon_{C'})$ under the algebra endomorphism of $C'$ obtained as the $p^v$-th convolution power of the identity map of $C'$.
--
--   This identifies the kernel of a transition map between two multiplicative-type finite flat group schemes with the ideal cutting out the $p^v$-torsion subscheme, descending the corresponding computation for group algebras along a faithfully flat trivialisation. It supplies the `ker_transition` condition required to assemble a [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199), and is used in the construction of the $p$-divisible group attached to the toric closure of the finite part of a Néron object at $p$ on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R]
    (A : Type) [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    (C C' : Type) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Free R C] [Module.Finite R C]
    [CommRing C'] [HopfAlgebra R C'] [Coalgebra.IsCocomm R C'] [Module.Free R C'] [Module.Finite R C']
    (Λ Λ' : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] [AddCommGroup Λ'] [Fintype Λ'] [DecidableEq Λ']
    (e : A ⊗[R] C ≃ₐc[A] AddMonoidAlgebra A Λ) (e' : A ⊗[R] C' ≃ₐc[A] AddMonoidAlgebra A Λ')
    (v : ℕ) (f : Λ' →+ Λ) (hf : Function.Surjective f) (hfker : ∀ x : Λ', f x = 0 ↔ ∃ y : Λ', x = (p ^ v) • y)
    (t : C' →ₐc[R] C) (ht : Function.Surjective t)
    (hte : ∀ z : A ⊗[R] C', e (Algebra.TensorProduct.map (AlgHom.id A A) (t : C' →ₐ[R] C) z) =
      AddMonoidAlgebra.mapDomainBialgHom A f (e' z)) :
    RingHom.ker t = PDivisibleGroup.Hopf.torsionIdeal R C' (p ^ v) := by sorry
