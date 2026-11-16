-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_8_19
-- name    : MatMulDS.Supplement.theorem_8_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:22:53.265869+00:00
-- url     : https://prove2.me/theorems/36e4199f-a1a2-435f-a1d0-aebd1775f6db
-- title:
--   Theorem 8.19 — additive-two spanner with $O(n^{3/2})$ edges for $m\le n^{9/5-\varepsilon}$ in $O_\varepsilon(n^{2-\xi})$ w.h.p.
-- statement:
--   Let $\beta$ be an admissible saving, fix $0<\varepsilon<3/10$, and set $\xi=\beta\varepsilon/16$. Using the bounds (3.3) of [Uzn26], there is a randomized algorithm that, given a connected undirected unweighted graph $G=(V,E)$ with $n\ge2$ vertices and $m\le n^{9/5-\varepsilon}$ edges, always returns a subgraph $H$ of $G$ with $O(n^{3/2})$ edges such that $d_H(u,v)$ is a $(1,2)$-approximation of $d_G(u,v)$ for all $u,v\in V$, that is,
--   $$d_G(u,v)\le d_H(u,v)\le d_G(u,v)+2,$$
--   and runs in $O_\varepsilon(n^{2-\xi})=O_\varepsilon(n^{2-0.0000166\varepsilon})$ time with high probability.
--
--   It is the first truly subquadratic construction of such spanners for $n^{3/2}\ll m\le n^{9/5-\varepsilon}$.
--
--   Differences from the source:
--   - encoding: a randomized algorithm on the word RAM → a program of the mission's machine over $\mathbb F_2$, whose coin instruction draws a uniform bit, every step counted, every word size $w\ge K\lceil\log_2(n+1)\rceil+K$; reason: a word RAM with random bits; the field cells over $\mathbb F_2$ are a bit array
--   - reading: "always returns" → every halting run, on every coin sequence, is correct, and the run halts with probability one; reason: a Las Vegas guarantee; "returns" implies halting
--   - reading: "with high probability" → for every $c>0$ a constant $C$ (depending on $c$) with probability at least $1-n^{-c}$; reason: the form the paper's own proofs give (Theorems E.4, E.5, Lemma J.2; SUPPLEMENT decision 1)
--   - reading: "Using the bounds (3.3) of [Uzn26]" → no hypothesis; reason: it names a cited theorem the proof uses; assuming it would weaken the statement (SUPPLEMENT decision 2)
--   - encoding: a graph $G=(V,E)$ with $n$ vertices and $m$ edges → $V=\{0,\dots,n-1\}$, any adjacency-list representation $L$ of $G$ as input words, $m$ the number of edges; reason: the source's input convention (§3: graphs given by adjacency lists)
--   - encoding: output $H$ with $O(n^{3/2})$ edges → word cell $0$ holds the number of listed pairs and cells $1+2t,2+2t$ the $t$-th pair; every pair is an edge of $G$; $H$ has at most $C_0n^{3/2}$ edges, $C_0$ fixed before $n$; reason: a layout; $O(\cdot)$ with its constant fixed first
--   - encoding: $O_\varepsilon$ → the program and all constants chosen after $\varepsilon$; reason: $\varepsilon$ is fixed in the statement
--   - encoding: the numerical form $O_\varepsilon(n^{2-0.0000166\varepsilon})$ → a separate conjunct, the inequality at $\beta=0.0002666$; reason: the source evaluates its bound at the admissible saving of Theorem 7.4
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 8.19, p.61 (PDF p.63)

import Mathlib
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_adjWords
import Definitions.Def_MatMulDS_Supplement_coinFrac

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 8.19, p.61** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `β` be an
admissible saving, fix `0 < ε < 3/10`, and set `ξ = βε/16`. Using the bounds (3.3) of [Uzn26], there is a randomized algorithm
that, given a connected undirected unweighted graph `G = (V, E)` with `n ≥ 2` vertices and `m ≤ n^{9/5−ε}` edges, always returns a
subgraph `H` of `G` with `O(n^{3/2})` edges such that `d_H(u, v)` is a `(1, 2)`-approximation of `d_G(u, v)` for all `u, v ∈ V`,
and runs in `O_ε(n^{2−ξ}) = O_ε(n^{2−0.0000166ε})` time with high probability.

**Formalization Note.**
* Randomized word RAM over `𝔽₂` (`coinFrac`), all steps counted, word size `w ≥ K⌈log₂(n+1)⌉ + K`; input `adjWords L`. Output:
  word cell `0` holds the number `k` of listed pairs and the cells `1 + 2t, 2 + 2t` the `t`-th pair; `H` is the graph of these
  pairs, every pair is an edge of `G`, `H` has at most `C₀ n^{3/2}` edges (`C₀` fixed before `n`), and
  `d_G(u, v) ≤ d_H(u, v) ≤ d_G(u, v) + 2` (the first inequality holds for every subgraph; `H` is connected).
* "Always returns" and "with high probability" as in Theorem 8.11 (`AlwaysReturns`; for every `c > 0` some `C`). The program and
  the constants depend on `ε` (`O_ε`).
* The numerical form `ξ ≥ 0.0000166 ε` at `β = 0.0002666` is the last conjunct. -/
theorem theorem_8_19 (β : ℝ) (hβ : AdmissibleSaving β) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 3 / 10) :
    (∃ (P : List AInstr) (K : ℕ) (C₀ : ℝ), 0 < C₀ ∧
      (∀ (n : ℕ), 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G L → G.Connected →
        (G.edgeSet.ncard : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 5 - ε) →
        ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
          AlwaysReturns P w (adjWords L) fun st =>
            ∃ es : List (Fin n × Fin n), (st 0).toInt = es.length ∧
              (∀ (t : ℕ) (ht : t < es.length),
                (st (1 + 2 * t)).toInt = ((es[t].1 : ℕ) : ℤ) ∧ (st (2 + 2 * t)).toInt = ((es[t].2 : ℕ) : ℤ)) ∧
              (∀ p ∈ es, G.Adj p.1 p.2) ∧
              ((edgesGraph es).edgeSet.ncard : ℝ) ≤ C₀ * (n : ℝ) ^ ((3 : ℝ) / 2) ∧
              ∀ u v : Fin n, (edgesGraph es).Reachable u v ∧
                G.dist u v ≤ (edgesGraph es).dist u v ∧ (edgesGraph es).dist u v ≤ G.dist u v + 2) ∧
      ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G L → G.Connected →
        (G.edgeSet.ncard : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 5 - ε) →
        ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
          1 - (n : ℝ) ^ (-c) ≤ coinFrac P w (adjWords L) ⌈C * (n : ℝ) ^ (2 - β * ε / 16)⌉₊ fun _ => True) ∧
    0.0000166 * ε ≤ 0.0002666 * ε / 16 := by sorry

end MatMulDS.Supplement
