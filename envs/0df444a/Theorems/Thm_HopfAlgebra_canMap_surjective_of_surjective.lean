-- Prove2me | Theorems.Thm_HopfAlgebra_canMap_surjective_of_surjective
-- name    : HopfAlgebra.canMap_surjective_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/403bfecd-7b40-55d5-9de6-cde28267aee8
-- title:
--   Surjectivity of the canonical map for a surjective Hopf map
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a commutative ring carrying a Hopf $R$-algebra structure, let $B$ be a commutative ring carrying an $R$-bialgebra structure, and let $\pi \colon A \to B$ be a morphism of $R$-bialgebras (a map that is simultaneously an $R$-algebra and an $R$-coalgebra homomorphism). Assume that $\pi$ is surjective as a function. The conclusion concerns the $R$-linear map [`HopfAlgebra.canMap`](def/HopfAlgebra_HopfKer.html#L34) $\pi \colon A \otimes_R A \to A \otimes_R B$, which by definition is the $R$-linear map underlying the $R$-algebra homomorphism [`HopfAlgebra.canAlgHom`](def/HopfAlgebra_HopfKer.html#L26) $\pi$; the latter is obtained from the universal property of the tensor product of commutative $R$-algebras applied to the two $R$-algebra maps $A \to A \otimes_R B$ given by $a \mapsto a \otimes 1$ on the left factor and by the coaction $\rho = (\mathrm{id}_A \otimes \pi) \circ \Delta_A$ on the right factor, so that on generators it sends $a \otimes a' \mapsto (a \otimes 1)\,\rho(a')$. The assertion is that this map is surjective as a function.
--
--   This is the surjectivity half of the statement that the canonical (shear, or Galois) map associated with a quotient $\pi \colon A \to B$ of commutative Hopf/bialgebra objects is an isomorphism; only surjectivity is claimed here, with no flatness, projectivity or finiteness hypotheses. It feeds into [`HopfAlgebra.finite_projective_hopfKer_of_surjective`](thm.html#HopfAlgebra.finite_projective_hopfKer_of_surjective) and [`HopfAlgebra.isHopfGalois_of_surjective`](thm.html#HopfAlgebra.isHopfGalois_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_canMap_surjective_of_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.canMap_surjective_of_surjective {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
    {B : Type*} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Function.Surjective (HopfAlgebra.canMap π) := by sorry
