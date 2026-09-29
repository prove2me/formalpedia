-- Prove2me | Theorems.Thm_HopfAlgebra_isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective
-- name    : HopfAlgebra.isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/71c1c0c9-7da4-5345-be5f-0f7c49ed7f85
-- title:
--   Hopf kernel of a surjection stays local and local-dual
-- statement:
--   Let $R$ be a commutative ring, and let $H$ and $HV$ be commutative rings equipped with Hopf algebra structures over $R$ that are finite and free as $R$-modules and whose comultiplications are cocommutative, with $HV$ nontrivial. Let $\pi : H \to HV$ be a morphism of $R$-bialgebras (an $R$-algebra map that is simultaneously a coalgebra map) and assume $\pi$ is surjective. Write $\mathrm{hopfKer}\,\pi$ for the $R$-subalgebra of $H$ on which the two algebra maps $H \to H \otimes_R HV$ given by $a \mapsto (\mathrm{id}_H \otimes \pi)(\Delta a)$ and $a \mapsto a \otimes 1$ agree, i.e. the equalizer defining the subalgebra of $\pi$-coinvariants, and assume it too is finite and free as an $R$-module. Assume further that $H$ is a local ring and that the Cartier dual $\mathrm{CartierDual}\,R\,H$, the $R$-module dual $\mathrm{Hom}_R(H,R)$ with its convolution ring structure, is a local ring. The conclusion is the conjunction: $\mathrm{hopfKer}\,\pi$ is a local ring, and $\mathrm{CartierDual}\,R\,(\mathrm{hopfKer}\,\pi)$ is a local ring.
--
--   In the language of finite flat group schemes this says that the kernel of a surjection of finite flat commutative group schemes over $\mathrm{Spec}\,R$ inherits the local-local property (connected with connected dual) from its ambient group scheme. It is used in the Dieudonné-module analysis of the bottom layer, via [`Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer`](thm.html#Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_HopfKerHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    (HV : Type) [CommRing HV] [HopfAlgebra R HV] [Module.Finite R HV] [Module.Free R HV]
    [Coalgebra.IsCocomm R HV] [Nontrivial HV]
    (π : H →ₐc[R] HV) (hπ : Function.Surjective π)
    [Module.Finite R ↥(HopfAlgebra.hopfKer π)] [Module.Free R ↥(HopfAlgebra.hopfKer π)]
    (hloc : IsLocalRing H) (hdual : IsLocalRing (CartierDual R H)) :
    IsLocalRing ↥(HopfAlgebra.hopfKer π) ∧ IsLocalRing (CartierDual R ↥(HopfAlgebra.hopfKer π)) := by sorry
