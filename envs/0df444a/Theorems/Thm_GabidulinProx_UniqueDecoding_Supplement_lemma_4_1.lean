-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_lemma_4_1
-- name    : GabidulinProx.UniqueDecoding.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:47:21.249108+00:00
-- url     : https://prove2.me/theorems/54e02d9b-e950-4d45-8d92-e6329d9179cd
-- title:
--   Lemma 4.1 — a far interleaved word has a far vector in its column span
-- statement:
--   Let $C=G(A,k)\subseteq L^n$ be an $[n,k,d]$ Gabidulin code over finite fields $K\subseteq L$, $q=|K|$, $q^m=|L|$, with $A$ $K$-linearly independent and $d=n-k+1$. Let $e$ be a positive integer with $e\le\lfloor(d-1)/2\rfloor$ and assume $q^m>q^{e+1}$. Let $U\in L^{n\times s}$ and let $\mathcal L\subseteq L^n$ be the $L$-span of the columns of $U$. The interleaved distance $d(U^T,C^s)$ is the minimum over $c_1,\dots,c_s\in C$ of the rank of the $s\times n$ matrix $U^T-[c_1;\dots;c_s]$ after expanding each entry over $K$ (the $K$-dimension of the span of its $n$ columns in $L^s$). If
--
--   $$d(U^T,C^s)>e,$$
--
--   then there exists $u\in\mathcal L$ with $d(u,C)>e$.
--
--   This is the first step of the soundness proof of Theorem 4.2.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: rank after expanding each entry in a fixed $\mathbb F_q$-basis of $\mathbb F_{q^m}$ → $K$-dimension of the $K$-span of the columns (published `wordRank`, `codeDistance`, `pairDistance`); reason: the matrix rank does not depend on the chosen basis; the pair distance is the joint column rank of the $2m\times n$ matrix
--   - encoding: an $[n,k,d]$ Gabidulin code $G(A,k)$ with $A$ $\mathbb F_q$-linearly independent and $d=n-k+1$ → $1\le k\le n$, a $K$-linearly independent family $\alpha:\mathrm{Fin}\,n\to L$, the published `gabidulin K α k`, and $d$ substituted by $n-k+1$; reason: the base mission's encoding; independence of $\alpha$ implies $n\le m$, and the paper fixes $d=n-k+1$ (Definition 2.4)
--   - encoding: $U\in\mathbb F_{q^m}^{n\times s}$, $d(U^T,C^s)$ (Definition 2.5) → `U : Fin n → Fin s → L` (row $r$ is `U r`) and the new `interleavedDistance`, a finite minimum over $s$-tuples of codewords of the joint column rank; reason: the interleaved distance is the rank of the $ms\times n$ expansion, minimized over $C^s$; never a maximum or sum of row distances
--   - encoding: $e\le\lfloor(d-1)/2\rfloor$ → $e\le(n-k)/2$ in natural division; reason: $d-1=n-k$ and natural division is the floor
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), §4.1 p.29 and Lemma 4.1 p.30; Definition 2.5 p.13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Lemma 4.1, p.30: let `C = G(A, k)` be an `[n, k, d]` Gabidulin code, `d = n - k + 1`,
`e` a positive integer with `e ≤ ⌊(d-1)/2⌋` and `q^m > q^(e+1)`. For `U ∈ L^{n×s}` whose
interleaved distance `d(Uᵀ, Cˢ)` exceeds `e`, some vector `u` of the `L`-span of the columns
of `U` satisfies `d(u, C) > e`. -/
theorem lemma_4_1 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    {n k e s : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (α : Fin n → L) (hα : LinearIndependent K α)
    (he : 1 ≤ e) (hed : e ≤ (n - k) / 2) (hqm : Fintype.card K ^ (e + 1) < Fintype.card L)
    (U : Fin n → Fin s → L) (hU : e < interleavedDistance K (gabidulin K α k) U) :
    ∃ u ∈ Submodule.span L (Set.range (fun j : Fin s => fun r : Fin n => U r j)),
      e < codeDistance K (gabidulin K α k) u := by sorry
end GabidulinProx.UniqueDecoding.Supplement
