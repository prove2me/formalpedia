-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/cab046dc-2ce8-534a-a6ca-f8601c98d0ed
-- title:
--   A simple zero of j(q^{Nq})-a on a strict second-kind disc
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N\neq 0$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}:A\to k$; let `data` be modular polynomial data for $q$ and `hKr` the Kronecker congruence asserting that the reduction of $\Phi$ modulo $q$ equals $(C(X)^{q}-X)(C(X)-X^{q})$, and let `hα`, `hβ` assert that the two inclusions $\overline{\mathbb Q}(X_0(N))\to\overline{\mathbb Q}(X_0(Nq))$, `heckeAlphaBar` and `heckeBetaBar`, are integral. Let $P$ be a `PlaceSpecialization` for these data (a map `sp` from places of `modularFunctionFieldBar N` to places of `modularFunctionFieldC k N` together with a map on degree-zero divisor classes and the listed compatibilities), assume $q\nmid N$, and let $R$ be a `ProlongationTuple` for $P$ satisfying `IsModel`, i.e. the two divisor laws (for $f$ lying in both prolongation valuation rings with non-zero residues, the push-forward of $\operatorname{div}(f)$ along `reduceFst`, respectively `reduceSnd`, restricted to the places strict of the first, respectively second, kind, computes at each place not fixed by the square of Frobenius the order of the corresponding residue function) together with the two cusp laws at the $\infty$- and $0$-sides. Let $v$ be a place of `modularFunctionFieldC k N` with $\varphi^{2}(v)\neq v$, where $\varphi$ is `frobOnPlacesGeomLevel`, which is affine in the sense that both $j$ and its level-$N$ $q$-expansion `jNGeomGen` lie in the valuation subring of $v$; let $c_2\in k$ satisfy $\operatorname{ord}_v(\mathrm{jNGeomGen}-c_2)=1$, and let $a\in A$ with $\mathrm{red}(a)=c_2$. Then there is a place $Q$ of `modularFunctionFieldBar (N*q)` over $\overline{\mathbb Q}$ which is strict of the second kind (that is, `reduceFst Q` $=\varphi(\mathrm{reduceSnd}\,Q)$ and $\varphi^{2}(\mathrm{reduceSnd}\,Q)\neq \mathrm{reduceSnd}\,Q$), with $\mathrm{reduceSnd}\,Q=v$, such that the element $j(\mathfrak q^{Nq})-a$ — the coefficient-wise base change to $\overline{\mathbb Q}$ of `qExpand ℚ (N*q) jq`, minus the image of $a$ — has order $1$ at $Q$, and order $0$ at every place $Q'\neq Q$ which is strict of the second kind with $\mathrm{reduceSnd}\,Q'=v$.
--
--   This exhibits, on the second-kind side and for the second moduli generator, a function with a single simple zero among the places of $\overline{\mathbb Q}(X_0(Nq))$ reducing to a given ordinary affine place $v$ of the special fibre, so that it serves as a local parameter on that residue disc. It is used to produce chart data at strict second-kind places and in the statement computing orders of places representing a divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictSnd_reduceSnd_eq_ord_jNQFun_sub_eq_one
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
      (P.IsStrictSnd Q ∧ P.reduceSnd Q = v ∧
        Q.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩ : ↥(modularFunctionFieldBar (N * q))) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 1) ∧
      ∀ Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictSnd Q' → P.reduceSnd Q' = v → Q' ≠ Q →
        Q'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩ : ↥(modularFunctionFieldBar (N * q))) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) = 0 := by sorry
