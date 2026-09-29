-- Prove2me | Theorems.Thm_HopfAlgebra_finiteType_hopfKer_of_finitePartIdempotent
-- name    : HopfAlgebra.finiteType_hopfKer_of_finitePartIdempotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/402e4cd9-1d91-59b9-8913-318bec582d7f
-- title:
--   Finite type of the Hopf kernel for a split quasi-finite pair
-- statement:
--   Let $R$ be a local principal ideal domain, $K$ a fraction field of $R$ of characteristic $0$, and let $H$ be a commutative Hopf $R$-algebra which is of finite type as an $R$-algebra, flat as an $R$-module, cocommutative as a coalgebra, and whose generic fibre $K \otimes_R H$ is a finite $K$-module; let $H'$ be a further commutative Hopf $R$-algebra, flat over $R$, and let $qc : H \to H'$ be a surjective morphism of Hopf $R$-algebras (coalgebra and algebra morphism). Assume given an idempotent $e \in H$ such that the localisation $H[1/e]$ is a finite $R$-module and the maximal ideal of $R$ generates the unit ideal of $H[1/(1-e)]$, an idempotent $e' \in H'$ with the same two properties relative to $H'$, and $qc(e) = e'$. Assume finally given an idempotent $f \in H$ lying in the Hopf kernel $\mathrm{hopfKer}\ qc$, that is, in the equaliser of the coaction $a \mapsto ((\mathrm{id} \otimes qc) \circ \Delta)(a)$ and $a \mapsto a \otimes 1$ as $R$-algebra maps $H \to H \otimes_R H'$, such that $f e = e$ and such that every $b \in \mathrm{hopfKer}\ qc$ with $b e = 0$ satisfies $b f = 0$. The conclusion is that the subalgebra $\mathrm{hopfKer}\ qc$ of $H$ is of finite type over $R$.
--
--   In geometric terms $G = \operatorname{Spec} H$ is a quasi-finite flat commutative group scheme over the local base $R$, split by $e$ into its finite part $\operatorname{Spec} H[1/e]$ and a complementary part with empty closed fibre, $N = \operatorname{Spec} H'$ is a flat closed subgroup split compatibly by $e'$, and $f$ cuts out the union of the finite part with its translates under $N$; the assertion is that the coordinate ring of the quotient-defining Hopf kernel $H^{\mathrm{co}\,H'}$ is again of finite type over $R$. It feeds the combined statement [`HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent`](thm.html#HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent), used in the construction of quotients of quasi-finite flat group schemes by flat closed subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_finiteType_hopfKer_of_finitePartIdempotent.lean

import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.finiteType_hopfKer_of_finitePartIdempotent
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
    Algebra.FiniteType R ↥(HopfAlgebra.hopfKer qc) := by sorry
