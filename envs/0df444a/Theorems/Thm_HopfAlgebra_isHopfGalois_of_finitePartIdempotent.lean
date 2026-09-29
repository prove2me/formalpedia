-- Prove2me | Theorems.Thm_HopfAlgebra_isHopfGalois_of_finitePartIdempotent
-- name    : HopfAlgebra.isHopfGalois_of_finitePartIdempotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/24210f90-902a-5a74-9d74-82318fd80016
-- title:
--   Hopf–Galois descent for a split quasi-finite pair over a local PID
-- statement:
--   Let $R$ be a local principal ideal domain with fraction field $K$ of characteristic $0$, let $H$ be a commutative Hopf $R$-algebra which is of finite type and flat over $R$, cocommutative as an $R$-coalgebra, with $K\otimes_R H$ a finite $K$-module, and let $H'$ be a commutative Hopf $R$-algebra, flat over $R$. Let $qc \colon H \to H'$ be a surjective homomorphism of $R$-bialgebras. Assume given idempotents $e \in H$ and $e' \in H'$ such that $R \to H[1/e]$ and $R \to H'[1/e']$ are module-finite, the maximal ideal of $R$ generates the unit ideal in $H[1/(1-e)]$ and in $H'[1/(1-e')]$, and $qc(e) = e'$. Assume further given an idempotent $f \in H$ lying in the Hopf kernel [`HopfAlgebra.hopfKer qc`](def/HopfAlgebra_HopfKer.html#L19), the equaliser of the coaction $(\mathrm{id}\otimes qc)\circ\Delta \colon H \to H \otimes_R H'$ and $a \mapsto a \otimes 1$, with $fe = e$ and such that every $b$ in the Hopf kernel with $be = 0$ satisfies $bf = 0$. Then $qc$ is Hopf–Galois in the sense of [`HopfAlgebra.IsHopfGalois`](def/HopfAlgebra_HopfKer.html#L66): the canonical $R$-linear map [`HopfAlgebra.canMap qc`](def/HopfAlgebra_HopfKer.html#L34) from $H \otimes_R H$ to $H \otimes_R H'$ is surjective, and every element of its kernel lies in the $R$-span of the balancing relations $(a h)\otimes a' - a \otimes (h a')$ with $a, a' \in H$ and $h$ in the Hopf kernel.
--
--   In geometric terms $\operatorname{Spec} H$ is a quasi-finite flat group scheme over the local base whose finite part is cut out by $e$, $\operatorname{Spec} H'$ a flat quotient, and $f$ is the idempotent of the orbit of the finite part; the conclusion is that the quotient is a Hopf–Galois extension, i.e. the canonical map $H \otimes_B H \to H \otimes_R H'$ over the Hopf kernel $B$ is an isomorphism. It feeds the combined statement [`HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent`](thm.html#HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent), which packages the Hopf–Galois property together with faithful flatness and finite type of the Hopf kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isHopfGalois_of_finitePartIdempotent.lean

import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isHopfGalois_of_finitePartIdempotent
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
    (hee' : qc e = e')
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0) :
    HopfAlgebra.IsHopfGalois qc := by sorry
