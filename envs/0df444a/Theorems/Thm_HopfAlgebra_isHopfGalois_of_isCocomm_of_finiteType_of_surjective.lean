-- Prove2me | Theorems.Thm_HopfAlgebra_isHopfGalois_of_isCocomm_of_finiteType_of_surjective
-- name    : HopfAlgebra.isHopfGalois_of_isCocomm_of_finiteType_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/2a95b5d2-a66b-547c-ad5a-125af6c05ff0
-- title:
--   Hopf–Galois property of surjections from cocommutative Hopf algebras
-- statement:
--   Let $k$ be a field, let $H$ be a commutative ring with a Hopf $k$-algebra structure which is of finite type as a $k$-algebra and whose comultiplication is cocommutative, let $H'$ be a commutative ring with a Hopf $k$-algebra structure, and let $qc \colon H \to H'$ be a morphism of $k$-bialgebras (a $k$-algebra map that is simultaneously a map of coalgebras) which is surjective as a function. Then $qc$ satisfies [`HopfAlgebra.IsHopfGalois`](def/HopfAlgebra_HopfKer.html#L66), that is, two things hold for the canonical map $\mathrm{can} =$ `canMap qc` $\colon H \otimes_k H \to H \otimes_k H'$, the underlying $k$-linear map of the canonical algebra homomorphism `canAlgHom qc`: first, $\mathrm{can}$ is surjective; second, every $z \in H \otimes_k H$ with $\mathrm{can}(z) = 0$ lies in the $k$-submodule spanned by the balancing relations, namely the elements $(a h) \otimes a' - a \otimes (h a')$ with $a, a' \in H$ and $h$ in the Hopf kernel `hopfKer qc`. Note that only the inclusion of $\ker \mathrm{can}$ into that span is asserted.
--
--   In geometric terms this is the affine quotient theorem: for a commutative affine algebraic group $G = \operatorname{Spec} H$ of finite type over a field and a closed subgroup scheme $N = \operatorname{Spec} H'$, the quotient map $G \to G/N$ is an $N$-torsor, equivalently the induced map $H \otimes_{H^{\mathrm{co}H'}} H \to H \otimes_k H'$ is an isomorphism; cocommutativity of $H$ makes every such quotient normal. It is proved via the criterion [`HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective`](thm.html#HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective), which reduces the Hopf–Galois condition to the ideal inclusion $\ker qc \subseteq H \cdot (\mathrm{hopfKer}\, qc)^{+}$, and it feeds the flatness and finiteness statement [`HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective`](thm.html#HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective) as well as [`HopfAlgebra.isHopfGalois_of_finitePartIdempotent`](thm.html#HopfAlgebra.isHopfGalois_of_finitePartIdempotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isHopfGalois_of_isCocomm_of_finiteType_of_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isHopfGalois_of_isCocomm_of_finiteType_of_surjective
    (k : Type) [Field k]
    (H : Type) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [Coalgebra.IsCocomm k H]
    (H' : Type) [CommRing H'] [HopfAlgebra k H']
    (qc : H →ₐc[k] H') (hqc : Function.Surjective qc) :
    HopfAlgebra.IsHopfGalois qc := by sorry
