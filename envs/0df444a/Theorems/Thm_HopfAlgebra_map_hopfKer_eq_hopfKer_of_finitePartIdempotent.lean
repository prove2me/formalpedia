-- Prove2me | Theorems.Thm_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent
-- name    : HopfAlgebra.map_hopfKer_eq_hopfKer_of_finitePartIdempotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/c8be94bf-38a5-512f-a9aa-9f92f4c902fe
-- title:
--   Invariants descend onto the invariants of the finite part
-- statement:
--   Let $R$ be a local principal ideal domain whose fraction field $K$ has characteristic $0$, let $H$ be a commutative Hopf $R$-algebra that is of finite type as an $R$-algebra, flat as an $R$-module and cocommutative, with $K \otimes_R H$ finite over $K$, and let $H'$ be a commutative Hopf $R$-algebra, flat over $R$. Let $qc : H \to H'$ be a surjective bialgebra map over $R$. Let $e \in H$ be idempotent with $\mathrm{Localization.Away}\ e$ finite over $R$ and with the maximal ideal of $R$ generating the unit ideal of $\mathrm{Localization.Away}\ (1-e)$, and let $e' \in H'$ satisfy the same two conditions with $qc(e) = e'$. Let $f \in H$ be idempotent, lying in $\mathrm{hopfKer}(qc)$ — the subalgebra of those $x \in H$ with $(\mathrm{id}_H \otimes qc)(\Delta x) = x \otimes 1$ in $H \otimes_R H'$ — with $f e = e$ and such that every $b \in \mathrm{hopfKer}(qc)$ with $be = 0$ satisfies $bf = 0$. Let $\pi_f : H \to H_f$ and $\pi_{f'} : H' \to H_{f'}$ be surjective bialgebra maps onto commutative Hopf $R$-algebras with kernels the ideals $(1-e)$ and $(1-e')$, and let $qc_f : H_f \to H_{f'}$ be a bialgebra map with $qc_f(\pi_f x) = \pi_{f'}(qc\, x)$ for all $x \in H$. Then the image of $\mathrm{hopfKer}(qc)$ under $\pi_f$ equals $\mathrm{hopfKer}(qc_f)$.
--
--   In the group-scheme dictionary, $H = \mathcal{O}(G)$ for a quasi-finite flat commutative group scheme over $R$ with flat closed subgroup $N$ cut out by $qc$, the idempotent $e$ carves out the finite part $G^f$, and $f$ is the orbit idempotent of $G^f \cdot N$; the assertion is that the $N$-invariant functions on $G$ restrict exactly onto the $N^f$-invariant functions on $G^f$. It feeds the faithful flatness of the quotient by the orbit idempotent used in the finite-part analysis of such group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.map_hopfKer_eq_hopfKer_of_finitePartIdempotent
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
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0)
    (Hf : Type) [CommRing Hf] [HopfAlgebra R Hf] (πf : H →ₐc[R] Hf) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker (πf : H →ₐ[R] Hf) = Ideal.span {1 - e})
    (Hf' : Type) [CommRing Hf'] [HopfAlgebra R Hf'] (πf' : H' →ₐc[R] Hf') (hπf' : Function.Surjective πf')
    (hkerf' : RingHom.ker (πf' : H' →ₐ[R] Hf') = Ideal.span {1 - e'})
    (qcf : Hf →ₐc[R] Hf') (hcomm : ∀ x : H, qcf (πf x) = πf' (qc x)) :
    (HopfAlgebra.hopfKer qc).map (πf : H →ₐ[R] Hf) = HopfAlgebra.hopfKer qcf := by sorry
