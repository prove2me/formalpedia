-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_3_6
-- name    : GabidulinProx.UniqueDecoding.lemma_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:31.270245+00:00
-- url     : https://prove2.me/theorems/bc954e4c-a87e-465b-9b84-e50c3a38e63e
-- title:
--   Lemma 3.6 — clearing denominators with controlled degrees
-- statement:
--   Let $C=G(A,k)\le L^n$ over finite fields $L/K$ with $q=|K|$, independent evaluation points, $1\le k\le n$, and $1\le e$ with $2e<n-k+1$. Let $u_0,u_1$ be arbitrary, let $S$ be their good-parameter set, and assume $|S|>\sigma_e$. Let $a_i,b_j$ satisfy the identity and all nonvanishing and degree conclusions of Lemma 3.4. For each $z\in S$, supply the decoded message $P_z$ with residual rank at most $e$. Construct $p_j$ as the ordinary Lagrange interpolant of the $X^{q^j}$ coefficient of $P_z$ on $S$, and write $P(X,Z)=\sum_{j<k}p_j(Z)X^{q^j}$. Put $S_0=\{z\in S:a_0(z)\ne0\}$ and $S_0(Z)=\prod_{z\in S_0}(Z-z)$.
--
--   There exists $\widetilde P(X,Z)=\sum_{j<k}\widetilde p_j(Z)X^{q^j}$ such that
--
--   $$\deg_Z\widetilde p_j\le(\sigma_e-1)\sigma_{k-1}+1\quad(j<k),$$
--   $$\widetilde P(X,Z)\equiv a_0(Z)^{\sigma_{k-1}}P(X,Z)\pmod{S_0(Z)}.$$
--
--   The congruence is coefficientwise. In addition, for every $z\in S_0$,
--
--   $$\widetilde P(X,z)=a_0(z)^{\sigma_{k-1}}P_z(X).$$
--
--   This gives both the polynomial congruence and its pointwise specialization, with the full source degree bound.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra embedding, $q=|K|$ and $m=[L:K]$; reason: finite extensions have the specified cardinality; independence of the evaluation points implies $n\le m$
--   - encoding: coordinates numbered $1,\ldots,n$ and $q$-degree $<k$ → coordinates indexed by $\mathrm{Fin}\,n$ and polynomials represented as $\sum_{i<k}c_iX^{q^i}$; reason: the reindexing and coefficient representation preserve every polynomial, including zero
--   - encoding: rank after expanding in a fixed base-field basis → $K$-dimension of the span of the columns, in $L$ or $L\times L$; reason: this is the same matrix rank independently of the chosen basis
--   - encoding: minimum distance to a code and its order-two interleaving → finite minima over a linear submodule $C$ and pairs in $C\times C$; reason: both indexing types are finite and nonempty because zero is a codeword; the pair uses joint column rank
--   - encoding: minimum distance $d=n-k+1$ and uniform denominator $q^m$ → $d$ is substituted by $n-k+1$ and the denominator is $|L|$; reason: the paper fixes the Gabidulin distance, and $|L|=|K|^{[L:K]}$
--   - encoding: bivariate $q$-linearized polynomials in $X$ with coefficients in $L[Z]$ → families of $X^{q^i}$-coefficients, with explicit specialization and evaluation maps; reason: these encode the same bivariate polynomials and retain polynomial rather than function identities
--   - encoding: polynomial degree bounds with zero polynomial of degree $-\infty$ → natural-degree inequalities against nonnegative bounds; reason: zero has natural degree zero and satisfies precisely the same upper bounds
--   - encoding: the coefficientwise congruence modulo $S_0(Z)$ → $S_0(Z)$ divides each $\widetilde p_j-a_0^{\sigma_{k-1}}p_j$; reason: divisibility is precisely congruence in the polynomial quotient; the Lagrange formula constructs the unique interpolants rather than selecting them from an existence theorem
--   - encoding: the unique decoded $P_z$ for $z\in S$ → a function $L\to L[X]$ constrained only on $S$ by membership and residual rank; reason: $2e<d$ makes each $P_z$ unique; values outside $S$ enter no statement
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Lemma 3.6 p.21; proof pp.21–22. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction

namespace GabidulinProx.UniqueDecoding

/-- Lemma 3.6, p.21. p_j is the constructed Lagrange interpolant, and S₀ is the
constructed regular subset. Divisibility states the coefficientwise congruence. -/
theorem lemma_3_6 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L) (a : Fin (e + 1) → Polynomial L)
    (b : Fin (k + e) → Polynomial L)
    (hAB : GlobalIdentity (Fintype.card K) α u₀ u₁ a b)
    (hbounds : GlobalBounds (Fintype.card K) a b)
    (hS : sigma (Fintype.card K) e < (goodParameters K α k e u₀ u₁).card)
    (Pz : L → Polynomial L)
    (hPz : DecodedFamily K α u₀ u₁ k e (goodParameters K α k e u₀ u₁) Pz) :
    let q := Fintype.card K
    let S := goodParameters K α k e u₀ u₁
    let S₀ := regularParameters S (a 0)
    let p := coefficientInterpolants q k S Pz
    ∃ pt : Fin k → Polynomial L,
      (∀ j, (pt j).natDegree ≤ clearingBound q k e) ∧
      (∀ j, rootProduct S₀ ∣ pt j - (a 0) ^ (sigma q (k - 1)) * p j) ∧
      ∀ z ∈ S₀, specialize q pt z = Polynomial.C ((a 0).eval z ^ (sigma q (k - 1))) * Pz z := by sorry

end GabidulinProx.UniqueDecoding
