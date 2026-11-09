-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_3_5
-- name    : GabidulinProx.UniqueDecoding.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:31.785004+00:00
-- url     : https://prove2.me/theorems/ba2f13e1-4095-4329-bb1e-e7a554423ff4
-- title:
--   Lemma 3.5 — specialization and symbolic composition
-- statement:
--   Let $C=G(A,k)\le L^n$ with $q=|K|$, independent evaluation points, $1\le k\le n$, and $1\le e$ with $2e<n-k+1$. Let coefficient families $a_i,b_j$ of the sizes in Lemma 3.4 satisfy its global identity. Fix any $z\in L$ and any $P\in\mathcal L(q,m,k)$ with $\operatorname{rk}_q(u_0+zu_1-P(A))\le e$. With $A_z=A(X,z)$ and $B_z=B(X,z)$,
--
--   $$A_z\circ P+B_z=0.$$
--
--   Thus the identity holds for the uniquely decoded $P_z$ at each good parameter. It includes the specialization where both $A_z$ and $B_z$ are zero.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra embedding, $q=|K|$ and $m=[L:K]$; reason: finite extensions have the specified cardinality; independence of the evaluation points implies $n\le m$
--   - encoding: coordinates numbered $1,\ldots,n$ and $q$-degree $<k$ → coordinates indexed by $\mathrm{Fin}\,n$ and polynomials represented as $\sum_{i<k}c_iX^{q^i}$; reason: the reindexing and coefficient representation preserve every polynomial, including zero
--   - encoding: rank after expanding in a fixed base-field basis → $K$-dimension of the span of the columns, in $L$ or $L\times L$; reason: this is the same matrix rank independently of the chosen basis
--   - encoding: minimum distance $d=n-k+1$ and uniform denominator $q^m$ → $d$ is substituted by $n-k+1$ and the denominator is $|L|$; reason: the paper fixes the Gabidulin distance, and $|L|=|K|^{[L:K]}$
--   - encoding: bivariate $q$-linearized polynomials in $X$ with coefficients in $L[Z]$ → families of $X^{q^i}$-coefficients, with explicit specialization and evaluation maps; reason: these encode the same bivariate polynomials and retain polynomial rather than function identities
--   - generalization: $a,b$ are the pair from Lemma 3.4, and $P_z$ is the unique decoded polynomial at $z\in S$ → any $a,b$ of those coefficient sizes satisfying the global identity and every message $P$ with residual rank at most $e$; reason: the degree bounds, global nonvanishing, and parameter-count condition are unused; closeness implies $z\in S$, so this includes every printed instance
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Lemma 3.5 p.21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction

namespace GabidulinProx.UniqueDecoding

/-- Lemma 3.5, p.21. Quantification over every close message also includes the
unique decoded message. The unused nonvanishing/degree conditions on a,b are omitted. -/
theorem lemma_3_5 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L) (a : Fin (e + 1) → Polynomial L)
    (b : Fin (k + e) → Polynomial L)
    (hAB : GlobalIdentity (Fintype.card K) α u₀ u₁ a b)
    (z : L) (P : Polynomial L) (hP : IsLinearized (Fintype.card K) k P)
    (hclose : wordRank K (linePoint u₀ u₁ z - evaluateWord α P) ≤ e) :
    (specialize (Fintype.card K) a z).comp P + specialize (Fintype.card K) b z = 0 := by sorry

end GabidulinProx.UniqueDecoding
