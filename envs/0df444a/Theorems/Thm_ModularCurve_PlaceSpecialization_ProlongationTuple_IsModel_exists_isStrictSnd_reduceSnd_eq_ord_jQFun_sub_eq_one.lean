-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jQFun_sub_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictSnd_reduceSnd_eq_ord_jQFun_sub_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/75f1b0d2-61fa-564d-b125-571246b9234d
-- title:
--   Unique strict second-kind place where j(q^q)-a vanishes simply
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A\to k$, a datum $data$ consisting of a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$ of $q$-expansions, a proof $hKr$ that the reduction of $\Phi$ modulo $q$ equals $(X^q-Y)(X-Y^q)$ in the bivariate normalisation used, and proofs $h\alpha$, $h\beta$ that the two degeneracy inclusions $\overline{\mathbb Q}(X_0(N))\to\overline{\mathbb Q}(X_0(Nq))$ (given by `heckeAlphaBar` and `heckeBetaBar` on the base-changed modular function fields) are integral. Let $P$ be a specialization datum `PlaceSpecialization` for these data, assume $q\nmid N$, let $R$ be a prolongation tuple for $P$ and assume $hR$: $R$ satisfies both divisor laws and both cusp laws. Let $v$ be a place of $k(X_0(N))=$ `modularFunctionFieldC k N` with $\varphi(\varphi(v))\neq v$, where $\varphi$ is the Frobenius map `frobOnPlacesGeomLevel` on places, with $v$ affine in the sense that both $j$ and $j_N$ lie in its valuation ring, and let $c_1\in k$ satisfy $\mathrm{ord}_v(j-c_1)=1$ and $a\in A$ satisfy $\mathrm{red}(a)=c_1$. Then there is a place $Q$ of $\overline{\mathbb Q}(X_0(Nq))$ which is strict of the second kind for $P$ (its first reduction equals $\varphi$ of its second reduction, and its second reduction is not fixed by $\varphi^2$), whose second reduction $P.\mathrm{reduceSnd}\,Q$ is $v$, with $\mathrm{ord}_Q\bigl(j(q^q)-a\bigr)=1$, where $j(q^q)$ is `ProlongationTuple.jQFun N q`, the pull-back of $j$ along the second degeneracy map; moreover every place $Q'\neq Q$ that is strict of the second kind with second reduction $v$ satisfies $\mathrm{ord}_{Q'}\bigl(j(q^q)-a\bigr)=0$.
--
--   The statement provides a uniformising coordinate on a residue disc of the second kind: over an affine place $v$ of the special fibre $X_0(N)_k$ not fixed by $\varphi^2$, exactly one strict second-kind place of $\overline{\mathbb Q}(X_0(Nq))$ reducing to $v$ carries a zero of $j(q^q)-a$, and that zero is simple. It is used to produce chart data at strict second-kind places and, combined with the divisor laws, to match orders of vanishing of modular functions across the two reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jQFun_sub_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictSnd_reduceSnd_eq_ord_jQFun_sub_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (R : ProlongationTuple P) (hR : R.IsModel)
    (v : Place k ↥(modularFunctionFieldC k N)) (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) (haff : IsAffineGeomPlace k N v)
    (c₁ : k) (hc : v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c₁) = 1) (a : A) (ha : red a = c₁) :
    ∃ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.IsStrictSnd Q ∧ P.reduceSnd Q = v ∧ Q.ord (ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 1) ∧
      ∀ Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd Q' → P.reduceSnd Q' = v → Q' ≠ Q →
        Q'.ord (ProlongationTuple.jQFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 0 := by sorry
