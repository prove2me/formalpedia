-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_two_list_coloring_poly
-- name    : KColoringFaster.ListBootstrap.two_list_coloring_poly
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:46.165627+00:00
-- url     : https://prove2.me/theorems/dd7cc512-2ef5-45bd-a838-9b08525931ce
-- title:
--   Proof of Theorem 5.2 — 2-list-coloring in polynomial time by 2-SAT [APT79]
-- statement:
--   List coloring with all lists of size at most $2$ is decidable deterministically, without error, in time polynomial in the input size, over an arbitrary palette of natural numbers. In other words, there is a deterministic polynomial-time algorithm that, given a graph $G$ with lists $L(v)\subseteq\mathbb N$, $|L(v)|\le 2$, decides whether $(G,L)$ has a list coloring.
--
--   This is the base case of the main theorem: it gives Theorem 5.2 for $k\le 2$ and supplies the $(k-1)$-list-coloring algorithm (of base $a=1$) that Theorem 5.1 needs for $k=3$. The source derives it from the polynomial-time algorithm for 2-SAT of Aspvall, Plass and Tarjan (1979).
--
--   **Formalization Note** Algorithms are as in the definition `Algorithms`: one program, cost at most a polynomial in the input bit size, no coins.
--
--   Differences from the source:
--   - encoding: "polynomial-time solvable" → one deterministic program with cost at most $p(\sigma)$ and registers of at most $q(\sigma)$ bits on the integer RAM; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - encoding: arbitrary palette → colors in $\mathbb N$; reason: any finite palette is numbered
--   - generalization: nonempty lists → lists may be empty; reason: instances with an empty list are not colorable and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 26, proof of Theorem 5.2 (unnumbered; cites Aspvall–Plass–Tarjan 1979)

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms

open Classical

namespace KColoringFaster.ListBootstrap

/-- Proof of Theorem 5.2, p. 26 (base case, via 2-SAT [APT79]): list coloring with all lists of size
at most `2` is decided deterministically, without error, in time polynomial in the input bit size,
over an arbitrary palette. -/
theorem two_list_coloring_poly :
    DetPolyDecides encList (MaxListLE 2) ListColorable := by sorry

end KColoringFaster.ListBootstrap
