-- Prove2me | Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
-- name    : HopfAlgebra.isHopfGalois_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/c0ffe1bf-3b71-5224-85aa-ea0187f0d199
-- title:
--   Surjections onto finite free Hopf algebras are Hopf–Galois
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a commutative ring carrying a Hopf $R$-algebra structure, and let $B$ be a commutative ring carrying a Hopf $R$-algebra structure which is finite and free as an $R$-module. Let $\pi \colon A \to B$ be a bialgebra homomorphism over $R$ (an $R$-algebra map compatible with comultiplication and counit), and suppose $\pi$ is surjective as a function. The conclusion is [`HopfAlgebra.IsHopfGalois π`](def/HopfAlgebra_HopfKer.html#L66), which by definition is the conjunction of two assertions about the canonical $R$-linear map $\operatorname{canMap} \pi \colon A \otimes_R A \to A \otimes_R B$ underlying the algebra homomorphism `canAlgHom π`: first, $\operatorname{canMap} \pi$ is surjective; second, every $z \in A \otimes_R A$ with $\operatorname{canMap} \pi (z) = 0$ lies in the $R$-submodule spanned by the set of balancing relations, namely the elements of the form $(a h) \otimes a' - a \otimes (h a')$ with $a, a' \in A$ and $h$ in `hopfKer π`. Thus $\operatorname{canMap} \pi$ is surjective with kernel exactly the span of the balancing relations, which is the Hopf–Galois condition in the form used throughout the development.
--
--   This is the theorem of Kreimer and Takeuchi that a surjection of commutative Hopf algebras onto a finite free one is a Hopf–Galois extension, the Hopf-algebraic form of the statement that $G \to G/H$ is an $H$-torsor for a finite locally free subgroup scheme $H$, here over an arbitrary base ring and with no hypothesis on $A$. It is used in the project's study of Hopf kernels and Cartier duality, for instance in the description of the elements annihilated by `hopfKer π` and in the construction of surjective bialgebra maps with prescribed Hopf kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isHopfGalois_of_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.isHopfGalois_of_surjective {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) : HopfAlgebra.IsHopfGalois π := by sorry
