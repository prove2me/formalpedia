-- Prove2me | Theorems.Thm_FourBlockIP_FPT_Supplement_theorem_13
-- name    : FourBlockIP.FPT.Supplement.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:15:48.822196+00:00
-- url     : https://prove2.me/theorems/e71585b3-6b42-49cf-bf20-7de1695363be
-- title:
--   Theorem 13 — Max-Min Fair Matching with size constraints is FPT parameterized by |V|
-- statement:
--   Let $k=|V|$ and let $|I|$ be the binary encoding length of an instance $I$ of Max-Min Fair Matching with size constraints (bipartite graph $G=(U\,\dot\cup\,V,E)$, colours $\mathcal C$ with $\mathrm{col}:U\to\mathcal C$, tolerance $\ell\ge0$, size bounds $q^-,q^+\in\mathbb Z$). There are a program $P$ of the mission's arithmetic RAM, a computable function $f:\mathbb N\to\mathbb N$ and a constant $c\in\mathbb N$, all fixed before the instance, such that for every instance $I$ the program $P$, started on the encoding of $I$, halts after at most
--
--   $$f(k)\cdot|I|^{c}$$
--
--   unit-cost operations, and outputs $[1]$ if there is an $\ell$-fair left-perfect many-to-one matching $M$ with $q^-\le|M(v)|\le q^+$ for all $v\in V$, and $[0]$ otherwise.
--
--   The parameter is $k$ alone: $f$ may not depend on $|U|$, $|\mathcal C|$, $\ell$ or $q^\pm$. Every instance is covered, including $k=0$, $U=\emptyset$, $\mathcal C=\emptyset$, negative $q^\pm$ and $\ell>|U|$. This answers the question of Boehmer and Koana whether fair matching with arbitrary size constraints is fixed-parameter tractable in $k$, for Max-Min fairness.
--
--   **Formalization Note** Time is the `cost` of the base mission's machine `FourBlockIP_FPT_Machine` (unit-cost integer and real arithmetic, comparisons and memory access; no oracle is called). A halted state is fixed by the step function, so the existence of one halting time with the stated cost and output fixes the output at every later time.
--
--   Differences from the source:
--   - reading: time measured on an unspecified machine → the number of unit-cost operations of the base mission's arithmetic RAM; reason: the paper fixes this convention on p. 3 and the proof on p. 21 obtains its bound from Theorem 2's operation count; no bit-complexity bound is claimed by the paper
--   - reading: encoding length of the instance → the binary length (with sign bits) of an explicit list of the six numbers, the colour set, the colouring and the adjacency matrix; reason: any standard encoding of the input graph, colour set and binary integers is within a factor polynomial in its length and a function of k of this one (an adjacency matrix has |U|·k entries, and every encoding names each u ∈ U), which f(k)·|I|^{O(1)} absorbs
--   - encoding: f(k)·|I|^{O(1)} → ∃ computable f : ℕ → ℕ, ∃ c : ℕ with cost ≤ f(k)·|I|^c, P, f, c chosen before every instance; reason: the standard uniform reading of FPT time
--   - encoding: a set M ⊆ E with exactly one edge at each u ∈ U → a map m : U → V with every pair (u, m u) an edge; reason: the two descriptions are in bijection
--   - encoding: max_c |M(v)_c| − min_c |M(v)_c| ≤ ℓ → |M(v)_c| − |M(v)_{c'}| ≤ ℓ for all c, c'; reason: equivalent for nonempty C; for empty C the max and min are undefined and then U is empty
--   - encoding: solving the decision problem → output [1] on yes-instances and [0] on no-instances; reason: the problem asks only whether a matching exists
--   - encoding: finite sets U, V, C, edge set E ⊆ U × V and an integer ℓ ≥ 0 → U = Fin |U|, V = Fin k, C = Fin |C|, E as a Bool adjacency function adj : U → V → Bool, ℓ : ℕ; reason: every instance is isomorphic to one of this form and the answer is invariant under renaming
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), Theorem 13, p. 20; proof p. 21; running-time convention p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf, SHA-256 6a8c564a99596cb456f614d44bf2506b1e9049dd12482fe67ba426616cf2df21

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Machine
import Definitions.Def_FourBlockIP_FPT_Supplement_FairMatching

namespace FourBlockIP.FPT.Supplement

open FourBlockIP.FPT

/-- Theorem 13, p. 20 (proof p. 21). One program `P`, one computable `f` and one exponent `c`,
chosen before every instance, decide Max-Min Fair Matching with size constraints on the
published arithmetic RAM (p. 3 time convention: arithmetic operations, no oracle queries),
within `f(|V|) · |I|^c` operations; output `[1]` on yes-instances and `[0]` otherwise. -/
theorem theorem_13 : ∃ P : Program, ∃ f : ℕ → ℕ, Computable f ∧ ∃ c : ℕ,
    ∀ I : FairMatchingInstance, ∃ t,
      let st := run P noOracle I.encode [] t
      halted P st = true ∧ st.cost ≤ f I.k * I.encLength ^ c ∧
        (I.IsYes → output st = [1]) ∧ (¬ I.IsYes → output st = [0]) := by sorry

end FourBlockIP.FPT.Supplement
