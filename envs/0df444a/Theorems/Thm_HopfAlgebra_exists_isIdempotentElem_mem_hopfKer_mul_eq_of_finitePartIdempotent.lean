-- Prove2me | Theorems.Thm_HopfAlgebra_exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent
-- name    : HopfAlgebra.exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/3e278651-2731-5987-812e-eb8e41d13db1
-- title:
--   Hopf-kernel idempotent dominating the finite-part idempotent
-- statement:
--   Let $R$ be a local principal ideal domain, $K$ its fraction field, assumed of characteristic $0$, and let $H$ be a commutative Hopf $R$-algebra which is of finite type as an $R$-algebra, flat as an $R$-module, cocommutative, and whose generic fibre $K \otimes_R H$ is a finite $K$-module. Let $H'$ be a further commutative Hopf $R$-algebra, flat over $R$, and let $qc : H \to H'$ be a surjective $R$-algebra-and-coalgebra homomorphism. Let $e \in H$ be idempotent with $H[1/e]$ finite as an $R$-module and with the maximal ideal of $R$ generating the unit ideal of $H[1/(1-e)]$, and let $e' \in H'$ be idempotent with the same two properties, and suppose $qc(e) = e'$. The assertion is that there exists an idempotent $f \in H$ such that $f$ lies in [`HopfAlgebra.hopfKer qc`](def/HopfAlgebra_HopfKer.html#L19), i.e. $f$ lies in the equalizer of the coaction $x \mapsto (\mathrm{id}_H \otimes qc)(\Delta x)$ and $x \mapsto x \otimes 1$ from $H$ to $H \otimes_R H'$, such that $f e = e$, and such that every $b$ in that equalizer subalgebra with $be = 0$ satisfies $bf = 0$.
--
--   Geometrically, $\operatorname{Spec} H$ is a quasi-finite flat group scheme over $R$ with finite part cut out by $e$, $\operatorname{Spec} H'$ a flat quotient, and $f$ is the indicator idempotent of the saturation of the finite part under the corresponding subgroup scheme: the smallest idempotent of the coinvariant subalgebra dominating $e$. It is used in the proof of [`HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent`](thm.html#HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent), where the Hopf kernel of $qc$ is shown to be faithfully flat, of finite type and Hopf–Galois.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent.lean

import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent
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
    ∃ f : H, IsIdempotentElem f ∧ f ∈ HopfAlgebra.hopfKer qc ∧ f * e = e ∧
      ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0 := by sorry
