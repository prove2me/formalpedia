-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_reduceFst_eq_ord_jNFun_sub_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_reduceFst_eq_ord_jNFun_sub_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/87a3cb9b-0b7b-5fde-9838-b7d56a862d42
-- title:
--   Simple zero of j_N-a on a strict first-kind disc
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A\to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` (the reduction of $\Phi$ modulo $q$ equals $(Y^q-X)(Y-X^q)$), and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of $\overline{\mathbb Q}$-modular function fields of level $N$ into level $Nq$. Let $P$ be a `PlaceSpecialization` for these data, assume $q\nmid N$, and let $R$ be a `ProlongationTuple` over $P$ satisfying `IsModel`, i.e. the two divisor laws and the two cusp laws. Let $v$ be a place of $\mathrm{modularFunctionFieldC}\,k\,N=k(j,j_N)$ over $k$ which is not fixed by the square of `frobOnPlacesGeomLevel` and which is affine, meaning that both generators `jGeomGen` and `jNGeomGen` lie in the valuation subring of $v$; let $c_2\in k$ satisfy $\mathrm{ord}_v(\mathrm{jNGeomGen}-c_2)=1$, and let $a\in A$ with $\mathrm{red}(a)=c_2$. Put $f=j_N-a$, the element of $\mathrm{modularFunctionFieldBar}(Nq)$ given by the coefficientwise image of the $q$-expansion $\mathrm{qExpand}\,\mathbb Q\,N\,jq$ minus the constant $a$. Then there is a place $Q$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ with `P.IsStrictFst Q` (Frobenius carries the first reduction of $Q$ to its second reduction, and the first reduction is not fixed by the square of Frobenius), with first reduction $P.\mathrm{reduceFst}\,Q=v$, and with $\mathrm{ord}_Q(f)=1$; moreover every place $Q'\neq Q$ satisfying `P.IsStrictFst` and $P.\mathrm{reduceFst}\,Q'=v$ has $\mathrm{ord}_{Q'}(f)=0$.
--
--   This is the second-generator companion of the statement that a lift of a uniformiser at an affine centre has a single simple zero in the corresponding residue disc: it provides the coordinate $j_N-a$ at centres where $j_N$, rather than $j$, is a uniformiser on the special fibre. It is used to produce chart data at strict first-kind places and in the identification of divisors of functions reduced along the first degeneracy map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_reduceFst_eq_ord_jNFun_sub_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_reduceFst_eq_ord_jNFun_sub_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (R : ProlongationTuple P) (hR : R.IsModel)
    (v : Place k ↥(modularFunctionFieldC k N)) (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) (haff : IsAffineGeomPlace k N v)
    (c₂ : k) (hc : v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c₂) = 1) (a : A) (ha : red a = c₂) :
    ∃ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.IsStrictFst Q ∧ P.reduceFst Q = v ∧
        Q.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_mul_right N q))⟩ : ↥(modularFunctionFieldBar (N * q))) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 1) ∧
      ∀ Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst Q' → P.reduceFst Q' = v → Q' ≠ Q →
        Q'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_mul_right N q))⟩ : ↥(modularFunctionFieldBar (N * q))) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 0 := by sorry
