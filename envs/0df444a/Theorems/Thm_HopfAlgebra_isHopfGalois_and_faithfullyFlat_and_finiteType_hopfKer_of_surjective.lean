-- Prove2me | Theorems.Thm_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective
-- name    : HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/c0f3489c-7463-5cd6-a513-44c1a2629c85
-- title:
--   Hopf–Galois property, faithful flatness and finite type of Hopf kernels
-- statement:
--   Let $R$ be a commutative ring which is a domain and a principal ideal ring, let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ which is of finite type and flat as an $R$-module and whose comultiplication is cocommutative, let $H'$ be a commutative ring carrying a Hopf algebra structure over $R$ and flat as an $R$-module, and let $qc \colon H \to H'$ be a homomorphism of $R$-bialgebras (simultaneously an algebra and a coalgebra map) which is surjective as a function. Write $K =$ [`HopfAlgebra.hopfKer qc`](def/HopfAlgebra_HopfKer.html#L19) for the $R$-subalgebra of $H$ consisting of those $a$ with $(\mathrm{id}_H \otimes qc)(\Delta a) = a \otimes 1$, i.e. the equalizer of the coaction $H \to H \otimes_R H'$ and the inclusion of the left factor. The conclusion is the conjunction of three assertions: first, [`HopfAlgebra.IsHopfGalois qc`](def/HopfAlgebra_HopfKer.html#L66), namely that the $R$-linear map `canMap qc` $\colon H \otimes_R H \to H \otimes_R H'$ underlying the canonical algebra homomorphism is surjective and that every element of its kernel lies in the $R$-span of the balancing relations $(ah) \otimes a' - a \otimes (ha')$ with $a, a' \in H$ and $h \in K$; second, that $H$ is faithfully flat as a $K$-module; third, that $K$ is of finite type as an $R$-algebra.
--
--   In scheme-theoretic terms this is the statement that, over a principal ideal domain, the quotient of a flat affine commutative group scheme of finite type by a flat closed subgroup scheme behaves well: $\operatorname{Spec} H \to \operatorname{Spec} K$ is a torsor under $\operatorname{Spec} H'$, is faithfully flat, and the base $\operatorname{Spec} K$ is again of finite type. It is used to identify the kernel ideal of a surjection of Hopf algebras in terms of the Hopf kernel, and in the analysis of primary torsion in Néron models attached to $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective.lean

import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc) :
    HopfAlgebra.IsHopfGalois qc ∧
      Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H ∧
      Algebra.FiniteType R ↥(HopfAlgebra.hopfKer qc) := by sorry
