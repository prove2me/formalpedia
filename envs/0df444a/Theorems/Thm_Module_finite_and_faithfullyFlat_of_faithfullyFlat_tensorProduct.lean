-- Prove2me | Theorems.Thm_Module_finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct
-- name    : Module.finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/10d24189-f74c-5acf-8882-c1baf8b13602
-- title:
--   Descent of finiteness and faithful flatness along faithfully flat base change
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a commutative ring equipped with an $R$-algebra structure which is faithfully flat as an $R$-module, and let $M$ be an $R$-module. Assume that the base change $W \otimes_R M$ is a finitely generated $W$-module and that it is faithfully flat as a $W$-module. The conclusion is the conjunction of two assertions about $M$ over the base $R$ itself: $M$ is a finitely generated $R$-module, and $M$ is a faithfully flat $R$-module, that is, $M$ is flat over $R$ and tensoring with $M$ detects vanishing, so that $M \otimes_R N = 0$ forces $N = 0$ for every $R$-module $N$. Note that $M$ is only assumed to be a module, with no algebra or finite-type hypothesis imposed beforehand; finiteness over $R$ is part of the conclusion rather than of the hypotheses.
--
--   This is the descent along a faithfully flat base change of the two properties 'finite' and 'faithfully flat' for modules; geometrically, for an affine $R$-scheme it says that finiteness, flatness and surjectivity over $\operatorname{Spec} R$ may be checked after a faithfully flat base change. It is used in the study of good reduction of Jacobians, in the construction of a finite faithfully flat cover with the required symmetry and local-isomorphism properties over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open TensorProduct

theorem Module.finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct
    {R : Type u} [CommRing R] (W : Type v) [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W]
    (M : Type w) [AddCommGroup M] [Module R M]
    [Module.Finite W (W ⊗[R] M)] [Module.FaithfullyFlat W (W ⊗[R] M)] :
    Module.Finite R M ∧ Module.FaithfullyFlat R M := by sorry
