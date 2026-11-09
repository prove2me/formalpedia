-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_2_2
-- name    : GabidulinProx.UniqueDecoding.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:09.799452+00:00
-- url     : https://prove2.me/theorems/4d9d4625-0af5-466e-9ea5-3015a31b1cc1
-- title:
--   Lemma 2.2 — interpolation of linearized polynomials
-- statement:
--   Let $L/K$ be a finite extension of finite fields with $q=|K|$, let $n\ge1$, and let $\alpha_1,\ldots,\alpha_n\in L$ be $K$-linearly independent. Let $T$ be any field extension of $L$. For arbitrary values $y_1,\ldots,y_n\in T$, there is a unique polynomial
--
--   $$f(X)=\sum_{i=0}^{n-1}c_iX^{q^i}\in T[X],\qquad f(\alpha_r)=y_r\quad(1\le r\le n).$$
--
--   Uniqueness is equality as polynomials, not only as functions. Taking $T=L$ gives the interpolation lemma; taking $T=L(Z)$ supports the polynomial identity on p.23.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra embedding, $q=|K|$ and $m=[L:K]$; reason: finite extensions have the specified cardinality; independence of the evaluation points implies $n\le m$
--   - encoding: coordinates numbered $1,\ldots,n$ and $q$-degree $<k$ → coordinates indexed by $\mathrm{Fin}\,n$ and polynomials represented as $\sum_{i<k}c_iX^{q^i}$; reason: the reindexing and coefficient representation preserve every polynomial, including zero
--   - generalization: the coefficients and prescribed values lie in $L$ → they may lie in any field extension $T/L$; reason: taking $T=L$ recovers every printed instance, and the same Moore matrix remains invertible after extending scalars
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Lemma 2.2 p.12; application over the rational function field p.23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Polynomials

namespace GabidulinProx.UniqueDecoding

/-- Lemma 2.2, p.12. Coefficients may lie in any extension field T of L, as needed
on p.23 over L(Z). This specializes to the printed result by T=L. -/
theorem lemma_2_2 {K L T : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] [Field T] [Algebra L T] {n : ℕ}
    (hn : 1 ≤ n) (α : Fin n → L) (hα : LinearIndependent K α) (y : Fin n → T) :
    ∃! f : Polynomial T, IsLinearized (Fintype.card K) n f ∧
      ∀ r, f.eval (algebraMap L T (α r)) = y r := by sorry

end GabidulinProx.UniqueDecoding
