-- Prove2me | Theorems.Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing
-- name    : HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/701781dc-afd6-5bce-bb9b-2f93f9f93923
-- title:
--   Faithful flatness of a Hopf algebra over a Hopf kernel
-- statement:
--   Let $R$ be a commutative ring which is an integral domain in which every ideal is principal, let $H$ be a commutative ring carrying a Hopf $R$-algebra structure which is of finite type as an $R$-algebra, flat as an $R$-module, and whose comultiplication is cocommutative, and let $H'$ be a commutative ring carrying a Hopf $R$-algebra structure and flat as an $R$-module. Let $qc \colon H \to H'$ be a bialgebra homomorphism over $R$ which is surjective as a function. Write $\mathrm{hopfKer}\,qc$ for the $R$-subalgebra of $H$ defined as the equaliser of the two $R$-algebra maps $H \to H \otimes_R H'$ given by $a \mapsto (\mathrm{id}_H \otimes qc)(\Delta a)$ and $a \mapsto a \otimes 1$, i.e. $\{a \in H : (\mathrm{id}\otimes qc)(\Delta a) = a \otimes 1\}$. The conclusion is that $H$ is a faithfully flat module over this subalgebra $\mathrm{hopfKer}\,qc$.
--
--   Geometrically, with $G = \operatorname{Spec} H$ a flat commutative affine $R$-group scheme of finite type, $N = \operatorname{Spec} H'$ a flat closed subgroup scheme and $\mathrm{hopfKer}\,qc = \mathcal{O}(G)^N$, this is the faithful-flatness half of the quotient theorem for flat affine group schemes over a one-dimensional base: $G \to G/N$ is faithfully flat. It feeds into [`HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective`](thm.html#HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective), and is obtained by combining the corresponding statement over a field with a fibrewise flatness criterion over residue fields of the principal ideal domain $R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc) :
    Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H := by sorry
