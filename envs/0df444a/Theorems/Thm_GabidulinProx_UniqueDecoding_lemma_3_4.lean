-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_3_4
-- name    : GabidulinProx.UniqueDecoding.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:23.832379+00:00
-- url     : https://prove2.me/theorems/30988d81-2f7c-45d6-857e-07ff78c6c513
-- title:
--   Lemma 3.4 — a global reconstruction with explicit degree bounds
-- statement:
--   Let $C=G(A,k)\le L^n$ for finite fields $L/K$ with $q=|K|$, independent evaluation points, and $1\le k\le n$. Let $1\le e$ and $2e<n-k+1$, and fix arbitrary words $u_0,u_1$. Put $S=\{z\in L:d(u_0+zu_1,C)\le e\}$. If $|S|>\sigma_e$, there exist coefficient families defining
--
--   $$A(X,Z)=\sum_{i=0}^ea_i(Z)X^{q^i},\qquad B(X,Z)=\sum_{j=0}^{k+e-1}b_j(Z)X^{q^j}$$
--
--   such that, for every evaluation point,
--
--   $$A(u_{0,r}+Zu_{1,r},Z)+B(\alpha_r,Z)=0.$$
--
--   Moreover $a_0\ne0$, $\deg_Za_i\le\sigma_e-q^i$ for every $0\le i\le e$, and $\deg_Zb_j\le\sigma_e$ for every $0\le j\le k+e-1$. The equations hold in $L[Z]$. This packages all pointwise reconstruction systems into one polynomial family.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra embedding, $q=|K|$ and $m=[L:K]$; reason: finite extensions have the specified cardinality; independence of the evaluation points implies $n\le m$
--   - encoding: coordinates numbered $1,\ldots,n$ and $q$-degree $<k$ → coordinates indexed by $\mathrm{Fin}\,n$ and polynomials represented as $\sum_{i<k}c_iX^{q^i}$; reason: the reindexing and coefficient representation preserve every polynomial, including zero
--   - encoding: rank after expanding in a fixed base-field basis → $K$-dimension of the span of the columns, in $L$ or $L\times L$; reason: this is the same matrix rank independently of the chosen basis
--   - encoding: minimum distance to a code and its order-two interleaving → finite minima over a linear submodule $C$ and pairs in $C\times C$; reason: both indexing types are finite and nonempty because zero is a codeword; the pair uses joint column rank
--   - encoding: minimum distance $d=n-k+1$ and uniform denominator $q^m$ → $d$ is substituted by $n-k+1$ and the denominator is $|L|$; reason: the paper fixes the Gabidulin distance, and $|L|=|K|^{[L:K]}$
--   - encoding: bivariate $q$-linearized polynomials in $X$ with coefficients in $L[Z]$ → families of $X^{q^i}$-coefficients, with explicit specialization and evaluation maps; reason: these encode the same bivariate polynomials and retain polynomial rather than function identities
--   - encoding: polynomial degree bounds with zero polynomial of degree $-\infty$ → natural-degree inequalities against nonnegative bounds; reason: zero has natural degree zero and satisfies precisely the same upper bounds
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Lemma 3.4 p.19; proof pp.19–21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction

namespace GabidulinProx.UniqueDecoding

/-- Lemma 3.4, p.19 (degree bounds proved p.21). S is the actual good-parameter set. -/
theorem lemma_3_4 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L)
    (hS : sigma (Fintype.card K) e < (goodParameters K α k e u₀ u₁).card) :
    ∃ (a : Fin (e + 1) → Polynomial L) (b : Fin (k + e) → Polynomial L),
      GlobalIdentity (Fintype.card K) α u₀ u₁ a b ∧ GlobalBounds (Fintype.card K) a b := by sorry

end GabidulinProx.UniqueDecoding
