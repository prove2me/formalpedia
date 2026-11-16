-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_Supplement_lemma_3_3
-- name    : KColoringFaster.ListBootstrap.Supplement.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:25:27.211176+00:00
-- url     : https://prove2.me/theorems/6f6d0658-0cfe-4846-9814-495d01f85e2e
-- title:
--   Lemma 3.3 — all induced list subinstances in $O^*(2^{|V(G)|})$ deterministic time
-- statement:
--   Fix a finite palette $P\subseteq\mathbb N$. There is a deterministic algorithm that, given a list-coloring instance $(G,L)$ on $n$ vertices with $L(v)\subseteq P$ for every vertex, determines simultaneously, for every $X\subseteq V(G)$, whether the induced subinstance $G[X]$ (with the lists restricted to $X$) is list colorable, in time
--   $$O^*\big(2^{n}\big).$$
--   The output is the full table of the $2^n$ answers, one per subset $X$, in the fixed order in which subset $X$ has index $\sum_{v\in X}2^v$.
--
--   This is the list-coloring extension of the result of Björklund, Husfeldt, Kaski and Koivisto that all $k$-colorable induced subgraphs are found in $O^*(2^n)$ time. In the paper it is the subroutine of the binary-list interpolation algorithm of Theorem 4.4.
--
--   **Formalization Note** The program and polynomials may depend on $P$ (the palette is fixed first) but not on the instance. "Time $O^*(2^n)$" means a coin-free run of cost at most $\lceil p(\sigma)\cdot 2^n\rceil$ with registers of at most $q(\sigma)$ bits, $\sigma$ the input bit size.
--
--   Differences from the source:
--   - reading: "one can determine … in O*(2^{|V(G)|}) time" (randomness not mentioned) → a deterministic algorithm; reason: the statement names no randomness, its proof is deterministic and Theorem 4.4 uses it deterministically; this is the stronger reading
--   - encoding: "determine simultaneously, for every X ⊆ V(G)" → the output is the 0/1 table indexed by the binary code of X; reason: a fixed output format for the same information
--   - encoding: O*(·) running time → one coin-free program of the integer RAM with cost at most ⌈p(σ)·2^n⌉ and registers of at most q(σ) bits; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - encoding: colors of an abstract palette P → P a finite set of natural numbers; reason: any finite palette is numbered
--   - encoding: vertex set V(G) → Fin n; reason: any n-vertex graph is relabeled by 0, …, n − 1
--   - generalization: nonempty lists → lists may be empty; reason: a vertex with an empty list makes exactly the subsets containing it uncolorable, and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 9, Lemma 3.3

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Supplement_DetTime

open Classical

namespace KColoringFaster.ListBootstrap.Supplement

open KColoringFaster.ListBootstrap

/-- Lemma 3.3, p. 9 (All induced list subinstances). Fix a palette `P`. One deterministic algorithm
computes, for a list instance on `G` with all lists contained in `P`, the whole table of which
induced subinstances `G[X]`, `X ⊆ V(G)`, are list colorable, in time `O*(2^{|V(G)|})`. -/
theorem lemma_3_3 (P : Finset ℕ) :
    DetComputes encList (OverPalette P) (fun I out => out = encSubsetTable I)
      (fun I => (2 : ℝ) ^ I.n) := by sorry

end KColoringFaster.ListBootstrap.Supplement
