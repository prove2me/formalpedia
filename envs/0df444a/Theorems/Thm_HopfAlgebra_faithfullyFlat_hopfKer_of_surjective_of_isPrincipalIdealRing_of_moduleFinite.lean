-- Prove2me | Theorems.Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite
-- name    : HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/cb82c19f-823b-5307-9596-5a0f31b152a3
-- title:
--   Faithful flatness over the Hopf kernel, finite flat case
-- statement:
--   Let $R$ be a commutative ring which is a domain and a principal ideal ring, let $H$ be a commutative ring carrying the structure of a Hopf $R$-algebra (no finiteness or flatness over $R$ is assumed), and let $H'$ be a commutative ring carrying the structure of a Hopf $R$-algebra which is in addition finite and flat as an $R$-module. Let $qc \colon H \to H'$ be a homomorphism of $R$-bialgebras and assume that the underlying function is surjective. Write $K =$ [`HopfAlgebra.hopfKer qc`](def/HopfAlgebra_HopfKer.html#L19) for the $R$-subalgebra of $H$ obtained as the equalizer of the two $R$-algebra maps $H \to H \otimes_R H'$ given by $a \mapsto (\mathrm{id}_H \otimes qc)(\Delta a)$ and $a \mapsto a \otimes 1$, i.e. the subalgebra of $H'$-coinvariants. The conclusion is that $H$, viewed as a module over $K$, is faithfully flat.
--
--   This is the affine quotient theorem in its finite flat case, in Hopf-algebra form: for a closed subgroup scheme $N = \operatorname{Spec} H'$, finite and flat over a principal ideal domain $R$, of the affine group scheme $G = \operatorname{Spec} H$, the map $G \to \operatorname{Spec} \mathcal{O}(G)^N$ is faithfully flat. It is used in the construction of quotients by idempotent-cut pieces of base-changed Hopf algebras, namely in [`HopfAlgebra.faithfullyFlat_quotient_span_one_sub_orbitIdempotent_baseChange_of_finitePartIdempotent`](thm.html#HopfAlgebra.faithfullyFlat_quotient_span_one_sub_orbitIdempotent_baseChange_of_finitePartIdempotent) and [`HopfAlgebra.faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent`](thm.html#HopfAlgebra.faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H]
    (H' : Type w) [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc) :
    Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H := by sorry
