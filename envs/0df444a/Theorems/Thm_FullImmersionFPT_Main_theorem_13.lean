-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_theorem_13
-- name    : FullImmersionFPT.Main.theorem_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:49:01.513386+00:00
-- url     : https://prove2.me/theorems/900bad8a-4545-4b11-bd36-df45a85d26e4
-- title:
--   Theorem 13 — under Assumption 12, free graphs reduce to signed graphs in O(k·ϕ(m)) time
-- statement:
--   Suppose Assumption 12 holds: a program $A$ which, given a signed graph $(G,\Sigma,t)$ with $m$ edges and a flooding $\mathcal C$, finds within $\varphi(m)$ steps either a flooding of greater value or a certificate of the same value as $\mathcal C$ such that every edge not forced by it lies in an infeasible circuit of some optimal flooding; as in the proof, $\varphi(m)\ge m$. Then, given a free graph $\mathcal G=(G,\Sigma,F,t)$ with $m$ edges and an integer $k$, one can find either a flooding of value at least $k$, or a flooding and a certificate of the same value, in time
--   $$O(k\cdot\varphi(m)).$$
--   Formally: there are a program $P$, a word-size factor $b$ and a constant $c$ (chosen after $A$ and $\varphi$) such that on every free graph and every $k\in\mathbb Z$, $P$ halts within $c\cdot\max(k,1)\cdot\varphi(m)+c$ steps with one of the two outputs. This reduces Theorem 3 to signed graphs.
--
--   Differences from the source:
--   - reading: "Suppose that Assumption 12 holds" (an algorithm running in time ϕ(|E(G)|)), and "Since ϕ(m) ⩾ m" in the proof → hypotheses Assumption12 A bA ϕ (one word-RAM program A with factor bA meeting Assumption 12 within ϕ(m) steps on every signed graph and flooding) and ∀ m, m ≤ ϕ m; reason: the assumption is about an algorithm, read on the same machine as the conclusion; the proof uses ϕ(m) ≥ m as part of the assumption
--   - reading: "an integer k", time O(k·ϕ(|E(G)|)) → every k : ℤ, within c·max(k, 1)·ϕ(m) + c steps; reason: for k ≥ 1 this is the printed bound; for k ≤ 0 O(k·ϕ) is meaningless (an output flooding must be written) and is read as O(ϕ(m))
--   - reading: "we can find/compute/test … in time O(k · ϕ(|E(G)|))" → one program P of the published TrulySubcubicAPSP word RAM and a word-size factor b, fixed before every input (and after A, bA, ϕ); on every input and every word size W ≥ b(⌊log₂(N+2)⌋+1) (FOMCMonDep.WordSizeOK, N = input length plus largest absolute entry) P halts within the explicit bound with a correct output; reason: the paper fixes a RAM storing graphs as adjacency lists of half-edges with constant-time access (p. 15) but names no formal machine; unit-cost word RAM with logarithmic words is the reading; each O(·) is an explicit constant chosen after the parameters it is subscripted with
--   - encoding: a graph given to the algorithm → an edge list on Fin n with half-edges (e, i) : Fin m × Fin 2 (inc (e, i) = ends e i, mate (e, i) = (e, 1 − i)) written as words (FreeCode.words, DecoCode.words); outputs are words in the cells after the input (RunsWithin, FOMCMonDep.Emits); reason: every finite multigraph with loops and parallel edges is isomorphic to such an edge list, and every edge order and orientation is allowed
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
--   - encoding: value(X, Σ′) = |E_{F,Σ′}(X)| + |δ(X)|/2 − odd_{Σ′}(G − X) → certValue in ℤ with (|δ(X)| : ℤ) / 2; reason: |δ(X)| is even in an Eulerian graph, so the division is exact; ℤ avoids truncated subtraction
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 15, Theorem 13 (with Assumption 12)

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Flooding

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Theorem 13** (p. 15). Suppose that Assumption 12 holds: a program `A` (word-size factor `bA`)
that, given a signed graph with `m` edges and a flooding, returns within `ϕ(m)` steps a flooding of
larger value or a certificate of the same value with the guarantee of Assumption 12 (the proof
uses `ϕ(m) ≥ m`). Then there are a program `P`, a factor `b` and a constant `c` such that, given a
free graph with `m` edges and an integer `k`, `P` finds within `c · max(k, 1) · ϕ(m) + c` steps
either a flooding of value at least `k`, or a flooding and a certificate of the same value. -/
theorem theorem_13 (A : List TrulySubcubicAPSP.Instr) (bA : ℕ) (ϕ : ℕ → ℕ)
    (hA : Assumption12 A bA ϕ) (hϕ : ∀ m : ℕ, m ≤ ϕ m) :
    ∃ (P : List TrulySubcubicAPSP.Instr) (b c : ℕ),
      ∀ (n m : ℕ) (Φ : FreeCode n m), Φ.toFree.IsFree → ∀ (k : ℤ) (W : ℕ),
        FOMCMonDep.WordSizeOK b (Φ.words ++ [k]) W →
        RunsWithin P W (c * (max k 1).toNat * ϕ m + c) (Φ.words ++ [k])
          (FloodOrCertOutput Φ k) := by sorry

end FullImmersionFPT.Main
