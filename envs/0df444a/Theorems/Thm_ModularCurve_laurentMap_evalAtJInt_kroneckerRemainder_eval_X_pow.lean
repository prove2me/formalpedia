-- Prove2me | Theorems.Thm_ModularCurve_laurentMap_evalAtJInt_kroneckerRemainder_eval_X_pow
-- name    : ModularCurve.laurentMap_evalAtJInt_kroneckerRemainder_eval_X_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/dd9757de-4aa9-5fad-b09f-2369fd8c42e4
-- title:
--   Kronecker congruence to second order in characteristic q
-- statement:
--   Let $q$ be a prime and let `data` be a `ModularPolynomialData q`, i.e. a monic $\Phi\in\mathbb Z[x][Y]$ of degree $\sum_{d\mid q,\ d\text{ squarefree}} q/d$ satisfying $\Phi(j,\,j_q)=0$ after substituting the rational $q$-expansions; `evalAtJInt` is the ring homomorphism $\mathbb Z[x]\to\mathbb Z((\mathfrak q))$ sending $x$ to $\jmath:=$ `jqInt`, the Laurent series $\mathfrak q^{-1}E_4^3\eta^{-24}$, and `qExpand ℤ q` is the endomorphism of $\mathbb Z((\mathfrak q))$ re-indexing exponents by multiplication by $q$. Assume $R\in\mathbb Z[x][Y]$ satisfies $\Phi=(C(x)^q-Y)\,(C(x)-Y^q)+q\,R$, and that $S\in\mathbb Z((\mathfrak q))$ satisfies $(\mathrm{qExpand}\ \mathbb Z\ q)(\jmath)-\jmath^{\,q}=q\,S$. Let $k$ be a field of characteristic $q$ and write $\bar{\ }$ for the coefficientwise map $\mathbb Z((\mathfrak q))\to k((\mathfrak q))$ induced by $\mathbb Z\to k$. Then, with $G(x):=R(x,x^q)\in\mathbb Z[x]$ obtained by substituting $Y\mapsto x^q$, $$\overline{G(\jmath)}\;=\;-\,\bar S\cdot\bigl(\bar\jmath^{\,q^{2}}-\bar\jmath\bigr)$$ in $k((\mathfrak q))$.
--
--   This is the second-order refinement of the Kronecker congruence $\Phi_q(x,Y)\equiv(x^q-Y)(x-Y^q) \bmod q$: it identifies the reduction mod $q$ of the remainder term, specialised along the Frobenius graph $Y=x^q$, as $-\bar S(\bar\jmath^{\,q^2}-\bar\jmath)$. It is used by [`ModularCurve.kroneckerRemainder_frobeniusGraph_ode`](thm.html#ModularCurve.kroneckerRemainder_frobeniusGraph_ode) in the analysis of the poles of $\bar G/(x^{q^2}-x)$, which detects supersingular $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_laurentMap_evalAtJInt_kroneckerRemainder_eval_X_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve

theorem ModularCurve.laurentMap_evalAtJInt_kroneckerRemainder_eval_X_pow
    (q : ℕ) [Fact q.Prime] (data : ModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
            + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (S : LaurentSeries ℤ) (hS : qExpand ℤ q jqInt - jqInt ^ q = (q : LaurentSeries ℤ) * S)
    (k : Type*) [Field k] [CharP k q] :
    laurentMap (Int.castRingHom k) (evalAtJInt (R.eval (Polynomial.X ^ q))) =
      - laurentMap (Int.castRingHom k) S *
        (laurentMap (Int.castRingHom k) jqInt ^ (q ^ 2) - laurentMap (Int.castRingHom k) jqInt) := by sorry
