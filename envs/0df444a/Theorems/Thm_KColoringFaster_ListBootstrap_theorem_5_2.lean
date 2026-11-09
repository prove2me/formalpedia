-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_theorem_5_2
-- name    : KColoringFaster.ListBootstrap.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:58.08181+00:00
-- url     : https://prove2.me/theorems/c06e899b-d38e-4193-a313-269452958dfe
-- title:
--   Theorem 5.2 — k-coloring and k-list-coloring in $O^*((2-\varepsilon_k)^n)$ time
-- statement:
--   For every fixed integer $k\ge 1$ there is an $\varepsilon_k>0$ such that
--
--   1. $k$-coloring of $n$-vertex graphs can be decided with one-sided error in
--   $$O^*\big((2-\varepsilon_k)^n\big)$$
--   time: a graph that is not $k$-colorable is always rejected, and a $k$-colorable graph is accepted with probability at least $1-e^{-n}$;
--   2. the same bound, with the same $\varepsilon_k$, holds for $k$-list-coloring over an arbitrary palette: given a graph on $n$ vertices with lists of at most $k$ natural-number colors, list colorability is decided with the same one-sided error in $O^*((2-\varepsilon_k)^n)$ time.
--
--   Here $O^*$ hides factors polynomial in the input size. Computing the chromatic number takes $O^*(2^n)$ time by the algorithm of Björklund, Husfeldt and Koivisto (2009); the theorem shows that for each fixed $k$ the decision problem "is $\chi(G)\le k$?" is exponentially faster.
--
--   **Formalization Note** Algorithms and $O^*$ are as in the definition `Algorithms`: one program and polynomials in the input bit size, fixed before the input; the cost bound holds on every coin string; the program has no oracle and its registers keep polynomially many bits. The input of $k$-coloring is the graph alone.
--
--   Differences from the source:
--   - reading: "exponentially small one-sided error" → no-instances always rejected, yes-instances accepted with probability at least $1-e^{-n}$; reason: $e^{-n}$ is the bound the proofs print (pp. 8, 25) and implies the other readings
--   - reading: "The same bound holds" → one $\varepsilon_k$ for both clauses; reason: the source's wording
--   - encoding: $O^*(\cdot)$ time → one program and polynomials $p,q$ fixed before the input, worst-case cost $\lceil p(\sigma)\,T\rceil$ on the integer RAM with registers of at most $q(\sigma)$ bits; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - encoding: arbitrary palette → colors in $\mathbb N$; reason: any finite palette is numbered
--   - generalization: nonempty lists → lists may be empty; reason: instances with an empty list are not colorable and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 26, Theorem 5.2

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms

open Classical

namespace KColoringFaster.ListBootstrap

/-- Theorem 5.2 (k-Coloring and List Coloring), p. 26. For every fixed integer `k ≥ 1` there is
`ε_k > 0` such that k-coloring is decided with one-sided error at most `e^{-n}` in `O*((2 - ε_k)^n)`
time, and so is k-list-coloring over an arbitrary palette (colors in `ℕ`, all lists of size at most
`k`), with the same `ε_k`. -/
theorem theorem_5_2 (k : ℕ) (hk : 1 ≤ k) :
    ∃ ε : ℝ, 0 < ε ∧
      RandDecides encGraph GraphInstance.n (fun _ => True) (GraphInstance.KColorable k)
        (fun g => (2 - ε) ^ g.n) (expErr 1) zeroErr ∧
      RandDecides encList ListInstance.n (MaxListLE k) ListColorable
        (fun I => (2 - ε) ^ I.n) (expErr 1) zeroErr := by sorry

end KColoringFaster.ListBootstrap
