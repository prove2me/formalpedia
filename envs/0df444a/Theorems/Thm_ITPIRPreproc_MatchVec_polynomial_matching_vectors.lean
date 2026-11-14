-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_polynomial_matching_vectors
-- name    : ITPIRPreproc.MatchVec.polynomial_matching_vectors
-- status  : Proved
-- author  : @Jesko
-- created : 2026-11-13T17:14:27.556173+00:00
-- url     : https://prove2.me/theorems/aefcfb3b-f71c-4171-affe-9668d0dbe3d5
-- title:
--   Appendix A — correctness, parity separation, and dimension of the polynomial matching vectors
-- statement:
--   Let $\ell,a,b,m,d$ be natural numbers, put $k=\max(2^a,3^b)-1$, and suppose $k\ge1$ and $\ell<2^a3^b$. Choose any $m$ distinct words $\sigma_r\in[\ell]^\ell$ and any enumeration by $[d]$ of all pairs $(I,\alpha)$ with $I\subseteq[\ell]$, $|I|\le k$, and $\alpha:I\to[\ell]$.
--
--   Use the CRT signal and binomial-inversion coefficients from the polynomial-construction definitions, and form
--   $$u_r(I,\alpha)=c_{|I|}\mathbf1[\sigma_r|_I=\alpha],\qquad v_r(I,\alpha)=\mathbf1[\sigma_r|_I=\alpha].$$
--   Then these vectors satisfy Equation (7): diagonal inner products are $1$ modulo $6$, and each off-diagonal inner product is $0$ modulo $2$ or modulo $3$. The vectors $v_r\bmod2$ are pairwise distinct. Moreover,
--   $$d=\sum_{t=0}^{k}\binom{\ell}{t}\ell^t,$$
--   and, when $\ell\ge1$, $d\le(k+1)\ell^{2k}$. Terms with $t>\ell$ vanish.
--
--   This is the algebraic and combinatorial correctness part of Appendix A. It is valid for any injective indexing of row words and any enumeration of coordinates; it does not assert a uniform RAM implementation or the final subpolynomial bound in terms of $h$.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, Appendix A, printed pp.36-37 (PDF pp.38-39), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/572.pdf

import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialConstruction
import Mathlib.Tactic
open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.PolynomialConstruction
open Finset

theorem ITPIRPreproc.MatchVec.polynomial_matching_vectors (ell a b m d : ℕ)
    (hk : 1 ≤ degree a b) (hsize : ell < 2^a * 3^b)
    (rows : Fin m ↪ (Fin ell → Fin ell))
    (coords : Fin d ≃ Coordinate ell (degree a b)) :
    IsMVFamily m d
      (fun r j => leftVector (coefficient ell a b) (rows r) (coords j))
      (fun r j => rightVector (rows r) (coords j)) ∧
    d = ∑ t ∈ range (degree a b + 1), ell.choose t * ell^t ∧
    (1 ≤ ell → d ≤ (degree a b + 1) * ell^(2 * degree a b)) := by sorry
