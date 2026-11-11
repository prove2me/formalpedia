-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_theorem_3
-- name    : FullImmersionFPT.Main.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:48:47.080825+00:00
-- url     : https://prove2.me/theorems/68bba463-bc87-439a-8f6c-d37a66b38217
-- title:
--   Theorem 3 — min-max theorem for floodings, and an O(km⁴) algorithm
-- statement:
--   Let $\mathcal G=(G,\Sigma,F,t)$ be a free graph. (1) The maximum value of a flooding equals the minimum value of a certificate:
--   $$\max_{\mathcal C}\mathrm{value}(\mathcal C)=\min_{(X,\Sigma')}\Big(|E_{F,\Sigma'}(X)|+\tfrac12|\delta(X)|-\mathrm{odd}_{\Sigma'}(G-X)\Big).$$
--   (2) Given $k\in\mathbb Z_+$ and an $m$-edge free graph, one can in $O(km^4)$ time find either a flooding of value at least $k$, or a flooding and a certificate of equal value: one program $P$, a factor $b$ and a constant $c$ with $P$ halting within $c\,k\,m^4+c$ steps. This is the algorithmic min-max theorem used throughout Part III.
--
--   Differences from the source:
--   - encoding: the maximum value of a flooding equals the minimum value of a certificate → there are a flooding C with value ≥ every flooding, a certificate (X, Σ′) with value ≤ every certificate, and value C = value(X, Σ′); reason: max and min are attained (finitely many, at least one of each), so this is the equality
--   - reading: "we can find/compute/test … in time O(km⁴)" → one program P of the published TrulySubcubicAPSP word RAM and a word-size factor b, fixed before every input; on every input and every word size W ≥ b(⌊log₂(N+2)⌋+1) (FOMCMonDep.WordSizeOK, N = input length plus largest absolute entry) P halts within the explicit bound with a correct output; reason: the paper fixes a RAM storing graphs as adjacency lists of half-edges with constant-time access (p. 15) but names no formal machine; unit-cost word RAM with logarithmic words is the reading; each O(·) is an explicit constant chosen after the parameters it is subscripted with
--   - encoding: a graph given to the algorithm → an edge list on Fin n with half-edges (e, i) : Fin m × Fin 2 (inc (e, i) = ends e i, mate (e, i) = (e, 1 − i)) written as words (FreeCode.words, DecoCode.words); outputs are words in the cells after the input (RunsWithin, FOMCMonDep.Emits); reason: every finite multigraph with loops and parallel edges is isomorphic to such an edge list, and every edge order and orientation is allowed
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
--   - encoding: value(X, Σ′) = |E_{F,Σ′}(X)| + |δ(X)|/2 − odd_{Σ′}(G − X) → certValue in ℤ with (|δ(X)| : ℤ) / 2; reason: |δ(X)| is even in an Eulerian graph, so the division is exact; ℤ avoids truncated subtraction
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 5, Theorem 3

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Flooding

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Theorem 3** (p. 5). (1) For every free graph, the maximum value of a flooding equals the
minimum value of a certificate: there are a flooding `C` of maximum value and a certificate
`(X, Σ′)` of minimum value, and their values are equal. (2) There are a program `P`, a factor `b`
and a constant `c` such that, given `k ∈ ℤ₊` and an `m`-edge free graph, `P` finds within
`c · k · m⁴ + c` steps either a flooding of value at least `k`, or a flooding and a certificate of
equal value. -/
theorem theorem_3 :
    (∀ (V H : Type) (Γ : FreeGraph V H), Γ.IsFree →
      ∃ (C : List (List H)) (X : Finset V) (S' : Finset (Sym2 H)),
        Γ.IsFlooding C ∧ Γ.IsCertificate X S' ∧ (Γ.floodValue C : ℤ) = Γ.certValue X S' ∧
        (∀ C', Γ.IsFlooding C' → Γ.floodValue C' ≤ Γ.floodValue C) ∧
        ∀ X' S'', Γ.IsCertificate X' S'' → Γ.certValue X S' ≤ Γ.certValue X' S'') ∧
    ∃ (P : List TrulySubcubicAPSP.Instr) (b c : ℕ),
      ∀ (n m : ℕ) (Φ : FreeCode n m), Φ.toFree.IsFree → ∀ (k W : ℕ), 0 < k →
        FOMCMonDep.WordSizeOK b (Φ.words ++ [(k : ℤ)]) W →
        RunsWithin P W (c * k * m ^ 4 + c) (Φ.words ++ [(k : ℤ)])
          (FloodOrCertOutput Φ k) := by sorry

end FullImmersionFPT.Main
