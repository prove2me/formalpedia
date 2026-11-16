-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_Supplement_theorem_4_4
-- name    : KColoringFaster.ListBootstrap.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:26:01.870763+00:00
-- url     : https://prove2.me/theorems/24ce9c54-4934-419d-a3d5-bb3b60492d08
-- title:
--   Theorem 4.4 — binary-list interpolation in $O^*(2^{n-b/\binom K2})$ deterministic time
-- statement:
--   Fix a finite palette $P\subseteq\mathbb N$ of size $K=|P|\ge 2$. For a list-coloring instance $(G,L)$ over $P$ (every $L(v)\subseteq P$) on $n$ vertices, let $b$ be the number of vertices whose list has size at most two. Then:
--
--   1. list colorability of $(G,L)$ can be decided deterministically, without error, in time
--   $$O^*\Big(2^{\,n-b/\binom{K}{2}}\Big);$$
--   2. a list coloring of $(G,L)$, when one exists, can be found deterministically within the same time bound.
--
--   The exponent is the real number $n-b/\binom K2$. Equivalently the bound is $O^*(2^{n-b}q_K^{\,b})$ with $q_K=2^{1-1/\binom K2}<2$: each vertex with a short list costs a factor $q_K$ instead of $2$. In the paper this is the black-box solver of the warm-up reduction (Lemma 4.2) and is stated independently of it.
--
--   **Formalization Note** The program and polynomials may depend on $P$ (the palette is fixed first) but not on the instance, on $n$ or on $b$. Time $O^*(T)$ means a coin-free run of cost at most $\lceil p(\sigma)\cdot T\rceil$ with registers of at most $q(\sigma)$ bits, $\sigma$ the input bit size. The recovered coloring is output as the list of the colors $c(0),\dots,c(n-1)$.
--
--   Differences from the source:
--   - encoding: O*(·) running time → one coin-free program of the integer RAM with cost at most ⌈p(σ)·2^{n−b/C(K,2)}⌉ and registers of at most q(σ) bits; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - encoding: colors of an abstract palette P → P a finite set of natural numbers; reason: any finite palette is numbered
--   - encoding: vertex set V(G) → Fin n; reason: any n-vertex graph is relabeled by 0, …, n − 1
--   - encoding: "a coloring can be recovered" → the output is the list c(0), …, c(n − 1) of a list coloring whenever one exists; reason: a fixed output format for the recovered coloring
--   - generalization: nonempty lists → lists may be empty; reason: instances with an empty list are not colorable, and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 19, Theorem 4.4

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Supplement_DetTime

open Classical

namespace KColoringFaster.ListBootstrap.Supplement

open KColoringFaster.ListBootstrap

/-- Theorem 4.4, p. 19 (Binary-list interpolation). Fix a palette `P` of size `K ≥ 2`. List
coloring of instances over `P` on `n` vertices, `b` of which have lists of size at most two, is
decided deterministically in time `O*(2^{n − b / (K choose 2)})`, and a coloring is recovered
within the same bound. -/
theorem theorem_4_4 (P : Finset ℕ) (hP : 2 ≤ P.card) :
    DetDecides encList (OverPalette P) ListColorable
        (fun I => (2 : ℝ) ^ ((I.n : ℝ) - (binaryCount I : ℝ) / ((P.card.choose 2 : ℕ) : ℝ))) ∧
      DetFinds encList (OverPalette P) IsColoringOutput
        (fun I => (2 : ℝ) ^ ((I.n : ℝ) - (binaryCount I : ℝ) / ((P.card.choose 2 : ℕ) : ℝ))) := by sorry

end KColoringFaster.ListBootstrap.Supplement
