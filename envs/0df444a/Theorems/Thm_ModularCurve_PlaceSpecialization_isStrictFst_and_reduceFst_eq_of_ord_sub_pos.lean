-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_and_reduceFst_eq_of_ord_sub_pos
-- name    : ModularCurve.PlaceSpecialization.isStrictFst_and_reduceFst_eq_of_ord_sub_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/c8f32019-eeda-5582-b76b-c7350aa3419e
-- title:
--   Congruent coordinate data force equal strict first reductions
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$; fix data $\mathit{data}$ consisting of a monic $\Phi \in \mathbb Z[X][X]$ of degree $\psi(q)$ annihilating $(j, j_q)$, together with a proof $h_{Kr}$ that $\Phi$ mod $q$ equals $(\mathrm{C}\,X^{q} - X)(\mathrm{C}\,X - X^{q})$, and proofs $h_\alpha, h_\beta$ that the two degeneracy embeddings $\overline{\mathbb Q}(X_0(N)) \to \overline{\mathbb Q}(X_0(Nq))$ (on the Laurent-series models `heckeAlphaBar`, `heckeBetaBar`) are integral. Let $P$ be a place-specialization packet for these data, assume $q \nmid N$ and that $\mathrm{red}\,c = 0$ holds exactly for $c$ in the maximal ideal of $A$. Let $Q$ be a place of $\overline{\mathbb Q}(X_0(Nq))$ which is strict of the first kind for $P$, i.e. the geometric-level Frobenius $\varphi$ carries $P.\mathrm{reduceFst}\,Q = P.\mathrm{sp}$ of the restriction of $Q$ along `heckeAlphaBar` to $P.\mathrm{reduceSnd}\,Q$ (the corresponding restriction along `heckeBetaBar`), while $\varphi^{2}(P.\mathrm{reduceFst}\,Q) \neq P.\mathrm{reduceFst}\,Q$. Assume moreover that some pair $(c_1,c_2) \in k \times k$ is a centre of $P.\mathrm{reduceFst}\,Q$, meaning $\operatorname{ord}(j - c_1) > 0$ and $\operatorname{ord}(j_N - c_2) > 0$ there for the generators `jGeomGen`, `jNGeomGen` of $k(X_0(N))$, and that $P.\mathrm{reduceFst}\,Q$ is the only place of $k(X_0(N))$ with that centre; assume also that the value of `jNGeomGen` at $P.\mathrm{reduceFst}\,Q$ is not fixed by raising to the $q^{2}$ power. Finally let $a,b,c,a',b',c' \in A$ satisfy $\mathrm{red}\,a' = \mathrm{red}\,a$, $\mathrm{red}\,b' = \mathrm{red}\,b$, $\mathrm{red}\,c' = \mathrm{red}\,c$, with $\operatorname{ord}_Q$ of $j - a$, $j_N - b$, $j_{Nq} - c$ all positive, and, for a further place $W$ of $\overline{\mathbb Q}(X_0(Nq))$, $\operatorname{ord}_W$ of $j - a'$, $j_N - b'$, $j_{Nq} - c'$ all positive, where $j$, $j_N$, $j_{Nq}$ denote `ProlongationTuple.jFun N q`, `jNFun N q`, `jNQFun N q`. Then $W$ is likewise strict of the first kind for $P$, and $P.\mathrm{reduceFst}\,W = P.\mathrm{reduceFst}\,Q$.
--
--   This is the rigidity half of the dictionary between points of the three-coordinate integral model $A[j, j_N, j_{Nq}]$ of $X_0(Nq)$ lying in the residue polydisc of a given centre and the places of $\overline{\mathbb Q}(X_0(Nq))$ that are strict of the first kind above that centre: congruent coordinate triples cannot separate such places. It is used in the construction of an element with prescribed nonvanishing reduction and integrality along all strict first-kind places, via [`ModularCurve.PlaceSpecialization.exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictFst`](thm.html#ModularCurve.PlaceSpecialization.exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictFst).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isStrictFst_and_reduceFst_eq_of_ord_sub_pos.lean

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

theorem ModularCurve.PlaceSpecialization.isStrictFst_and_reduceFst_eq_of_ord_sub_pos
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictFst Q)
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceFst Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceFst Q)
    (hgen : (P.reduceFst Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst Q).evalAt (jNGeomGen k N))
    (a b c a' b' c' : A) (ha : red a' = red a) (hb : red b' = red b) (hc : red c' = red c)
    (haQ : 0 < Q.ord (PlaceSpecialization.ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)))
    (hbQ : 0 < Q.ord (PlaceSpecialization.jNFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ)))
    (hcQ : 0 < Q.ord (PlaceSpecialization.jNQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (haW : 0 < W.ord (PlaceSpecialization.ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a' : AlgebraicClosure ℚ)))
    (hbW : 0 < W.ord (PlaceSpecialization.jNFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b' : AlgebraicClosure ℚ)))
    (hcW : 0 < W.ord (PlaceSpecialization.jNQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c' : AlgebraicClosure ℚ))) :
    P.IsStrictFst W ∧ P.reduceFst W = P.reduceFst Q := by sorry
