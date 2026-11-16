-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_theorem_4_2
-- name    : GabidulinProx.UniqueDecoding.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:47:44.166724+00:00
-- url     : https://prove2.me/theorems/748c6e63-4af8-456e-9794-201968695b0a
-- title:
--   Theorem 4.2 — soundness of the IOPP for interleaved Gabidulin codes
-- statement:
--   Let $C=G(A,k)\subseteq L^n$ be a Gabidulin code over finite fields $K\subseteq L$ ($q=|K|$, $q^m=|L|$, $1\le k\le n$, $A$ $K$-linearly independent), so that the interleaved code $C^s$ has minimum distance $d=n-k+1$, and let $e$ be a positive integer with $e<d/2$. Let $\varepsilon_e=\tau_e/q^m$ as in Theorem 3.3, where $\sigma_r=\sum_{i=0}^rq^i$ and $\tau_e=(\sigma_e-1)+\sigma_e((\sigma_e-1)\sigma_{k-1}+1)$. Consider the IOPP of §4.1 with oracle $U^*\in L^{n\times s}$:
--
--   1. the verifier sends a uniformly random $a\in L^s$;
--   2. the prover sends $u\in L^n$, an arbitrary function of $a$;
--   3. the verifier samples a uniformly random set of $t$ distinct positions $\{j_1,\dots,j_t\}\subseteq[n]$ ($t\le n$);
--   4. the verifier accepts iff $u\in C$ and $u_{j_\ell}=a\cdot U^*(j_\ell)^T$ for all $\ell$.
--
--   If $d((U^*)^T,C^s)>e$, then for every prover strategy
--
--   $$\Pr[\text{V accepts}]\le\Bigl(1-\frac en\Bigr)^t+\varepsilon_e .$$
--
--   No hypothesis $q^{e+1}<q^m$ is made.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: rank after expanding each entry in a fixed $\mathbb F_q$-basis of $\mathbb F_{q^m}$ → $K$-dimension of the $K$-span of the columns (published `wordRank`, `codeDistance`, `pairDistance`); reason: the matrix rank does not depend on the chosen basis; the pair distance is the joint column rank of the $2m\times n$ matrix
--   - encoding: an $[n,k,d]$ Gabidulin code $G(A,k)$ with $A$ $\mathbb F_q$-linearly independent and $d=n-k+1$ → $1\le k\le n$, a $K$-linearly independent family $\alpha:\mathrm{Fin}\,n\to L$, the published `gabidulin K α k`, and $d$ substituted by $n-k+1$; reason: the base mission's encoding; independence of $\alpha$ implies $n\le m$, and the paper fixes $d=n-k+1$ (Definition 2.4)
--   - encoding: "$U^*$ is rejected except with probability $p$" for any malicious prover $P^*$ → for every function $P:L^s\to L^n$, the exact acceptance probability `acceptProb` over uniform $a\in L^s$ and a uniform $t$-subset of $\mathrm{Fin}\,n$ is at most $p$; reason: the prover speaks once, before the queries, so its message is a function of $a$; a randomized prover's acceptance probability is an average of deterministic ones
--   - encoding: $t$ positions sampled uniformly from $[n]$ → a uniform element of `powersetCard t univ`, with $t\le n$; reason: the proof's count $\binom{n-e-1}{t}/\binom nt$ is for $t$ distinct positions, which requires $t\le n$
--   - encoding: $d((U^*)^T,C^s)$ → the new `interleavedDistance`; reason: as in Lemma 4.1
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), IOPP protocol box p.30 and Theorem 4.2 p.31; ε_e from Theorem 3.3 p.19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Theorem 4.2, p.31: let `C = G(A, k)` (`1 ≤ k ≤ n`), so `Cˢ` has minimum distance
`d = n - k + 1`, and `e` a positive integer with `e < d/2`. If `d((U*)ᵀ, Cˢ) > e`, then for
every prover strategy `P` (its message as a function of the challenge `a ∈ L^s`) the IOPP
verifier of p.30, with `t` uniformly random distinct query positions, accepts with probability
at most `(1 - e/n)^t + ε_e`, where `ε_e = τ_e/q^m` as in Theorem 3.3. -/
theorem theorem_4_2 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    {n k e s t : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (α : Fin n → L) (hα : LinearIndependent K α)
    (he : 1 ≤ e) (hed : 2 * e < n - k + 1) (ht : t ≤ n)
    (U : Fin n → Fin s → L) (hU : e < interleavedDistance K (gabidulin K α k) U)
    (P : (Fin s → L) → (Fin n → L)) :
    acceptProb (gabidulin K α k) U t P ≤
      (1 - (e : ℝ) / (n : ℝ)) ^ t +
        (tau (Fintype.card K) k e : ℝ) / (Fintype.card L : ℝ) := by sorry
end GabidulinProx.UniqueDecoding.Supplement
