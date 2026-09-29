-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos
-- name    : ModularCurve.PlaceSpecialization.isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/74287860-0d0a-51f3-8805-851691f3a83e
-- title:
--   Places congruent to a strict second-kind place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A \to k$, modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$, and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of $\overline{\mathbb Q}$-modular function fields of level $N$ into level $Nq$. Let $P$ be a place-specialisation packet for these data, and assume $q \nmid N$ and that $\ker(\mathrm{red})$ is exactly the maximal ideal of $A$. Let $Q$ be a place of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$ which is strict of the second kind for $P$, meaning that $P$'s first reduction of $Q$ is the geometric Frobenius image of its second reduction $\bar v = P.\mathrm{reduceSnd}\,Q$ (a place of `modularFunctionFieldC k N`) and that applying that Frobenius twice to $\bar v$ does not return $\bar v$. Assume further that some pair $(c_1,c_2) \in k \times k$ is a centre of $\bar v$, in the sense that $\mathrm{ord}_{\bar v}(\tilde\jmath - c_1) > 0$ and $\mathrm{ord}_{\bar v}(\tilde\jmath_N - c_2) > 0$ for the generators `jGeomGen k N`, `jNGeomGen k N`, and that $\bar v$ is the only place of `modularFunctionFieldC k N` with this centre; assume also that the residue values of these two generators at $\bar v$ are not fixed by raising to the power $q^2$. Finally let $a,b,c,a',b',c' \in A$ satisfy $\mathrm{red}\,a' = \mathrm{red}\,a$, $\mathrm{red}\,b' = \mathrm{red}\,b$, $\mathrm{red}\,c' = \mathrm{red}\,c$, let $\mathrm{ord}_Q$ be positive on $j(q\tau) - a$, $j(Nq\tau) - b$ and $j - c$ (the elements `ProlongationTuple.jQFun N q`, `jNQFun N q`, `ProlongationTuple.jFun N q`), and let $W$ be a further place of `modularFunctionFieldBar (N * q)` with $\mathrm{ord}_W$ positive on the same three functions shifted by $a'$, $b'$, $c'$ respectively. Then $W$ is also strict of the second kind for $P$, and $P.\mathrm{reduceSnd}\,W = P.\mathrm{reduceSnd}\,Q$.
--
--   This is the rigidity half of the dictionary between $A$-points of the three-coordinate integral model of $X_0(Nq)$ with coordinates $j(q\tau)$, $j(Nq\tau)$, $j$ lying in a fixed residue polydisc and the places of the level-$Nq$ function field that are strict of the second kind: congruence of the three coordinates modulo the maximal ideal of $A$ forces the same second reduction. It is used in [`ModularCurve.PlaceSpecialization.exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd`](thm.html#ModularCurve.PlaceSpecialization.exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Definitions.Def_MDivRepresents

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q)
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q)
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (a b c a' b' c' : A) (ha : red a' = red a) (hb : red b' = red b) (hc : red c' = red c)
    (haQ : 0 < Q.ord (PlaceSpecialization.ProlongationTuple.jQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)))
    (hbQ : 0 < Q.ord (PlaceSpecialization.jNQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ)))
    (hcQ : 0 < Q.ord (PlaceSpecialization.ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (haW : 0 < W.ord (PlaceSpecialization.ProlongationTuple.jQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a' : AlgebraicClosure ℚ)))
    (hbW : 0 < W.ord (PlaceSpecialization.jNQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b' : AlgebraicClosure ℚ)))
    (hcW : 0 < W.ord (PlaceSpecialization.ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c' : AlgebraicClosure ℚ))) :
    P.IsStrictSnd W ∧ P.reduceSnd W = P.reduceSnd Q := by sorry
