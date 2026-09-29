-- Prove2me | Theorems.Thm_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent
-- name    : HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a689ff7e-1470-5a51-9de5-af6ef490b151
-- title:
--   Hopf–Galois descent along a quotient with split finite part
-- statement:
--   Let $R$ be a local principal ideal domain, $K$ a fraction field of $R$ of characteristic $0$, and let $H$ be a commutative Hopf $R$-algebra which is of finite type as an $R$-algebra, flat as an $R$-module, cocommutative as a coalgebra, and whose generic fibre $K \otimes_R H$ is a finite $K$-module; let $H'$ be a flat commutative Hopf $R$-algebra and $qc : H \to H'$ a surjective morphism of $R$-coalgebra-algebras (a bialgebra map). Assume given idempotents $e \in H$ and $e' \in H'$ with $qc(e) = e'$ such that the localisations $H[1/e]$ and $H'[1/e']$ are finite $R$-modules, while the maximal ideal of $R$ generates the unit ideal in $H[1/(1-e)]$ and in $H'[1/(1-e')]$. Write $B = \mathrm{hopfKer}\,qc$ for the subalgebra of $h \in H$ with $(\mathrm{id} \otimes qc)(\Delta h) = h \otimes 1$. Then: the canonical algebra map $H \otimes_R H \to H \otimes_R H'$ is surjective and its kernel lies in the $R$-span of the balancing relations $(ab) \otimes a' - a \otimes (b a')$ with $b \in B$; $H$ is faithfully flat as a $B$-module; and $B$ is of finite type over $R$.
--
--   This is the local structure theorem for a quotient of a quasi-finite flat commutative group scheme over a local Dedekind base in the case where the finite part is cut out by an idempotent: the quotient map is Hopf–Galois and the Hopf kernel is a well-behaved base for descent. It is the split-case input to the corresponding statement for an arbitrary surjection of flat Hopf algebras with module-finite generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent.lean

import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (e' : H') (he' : IsIdempotentElem e') (hfin' : Module.Finite R (Localization.Away e'))
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (IsLocalRing.maximalIdeal R) = ⊤)
    (hee' : qc e = e') :
    HopfAlgebra.IsHopfGalois qc ∧
      Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H ∧
      Algebra.FiniteType R ↥(HopfAlgebra.hopfKer qc) := by sorry
