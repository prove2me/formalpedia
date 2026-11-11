-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_lemma_26
-- name    : FullImmersionFPT.Main.lemma_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:49:13.386738+00:00
-- url     : https://prove2.me/theorems/c2effa59-2cbc-4529-b8db-ee63c603c138
-- title:
--   Lemma 26 — the τ-color-folio in linear time at bounded treewidth
-- statement:
--   For decorated graphs of bounded treewidth the $\tau$-color-folio is computable in linear time: for every $\tau\in\mathbb N$ and every bound $f_{26}(\tau,r_G,|U|,q)$ on the treewidth, the $\tau$-color-folio $C_\tau(\mathcal G)$ of a decorated graph $\mathcal G$ with $r_G$ roots, labels in $\mathbb F_2^U$, colors in $[q]$ and treewidth at most $f_{26}(\tau,r_G,|U|,q)$ can be found in time
--   $$O_{\tau,r_G,|U|,q}(n).$$
--   Formally: one program $P$ (input: the code of $\mathcal G$ and $\tau$) such that for all $\tau,r_G,|U|,q$ and every width bound $w$ there is $c$ with $P$ outputting $C_\tau(\mathcal G)$, up to equivalence, within $c\,n+c$ steps on every such $\mathcal G$ of treewidth at most $w$. It is the base case of Proposition 24.
--
--   Differences from the source:
--   - generalization: "For any τ ∈ N, suppose there exists a function f26 : N⁴ → N such that the treewidth of a decorated graph G is at most f26(τ, r_G, |U|, q). Then the τ-color-folio of G can be found in time O_{τ,r_G,|U|,q}(n)" → one program P for all τ and all treewidth bounds w, with c chosen after (τ, r_G, |U|, q, w): within c·n + c steps on every decorated graph with these parameters and treewidth at most w; reason: fixing τ and f26 and taking w = f26(τ, r_G, |U|, q) gives the printed statement; the uniform program is what the main algorithm uses
--   - reading: "we can find/compute/test … in time O_{τ,r_G,|U|,q}(n)" → one program P of the published TrulySubcubicAPSP word RAM and a word-size factor b, fixed before every input; on every input and every word size W ≥ b(⌊log₂(N+2)⌋+1) (FOMCMonDep.WordSizeOK, N = input length plus largest absolute entry) P halts within the explicit bound with a correct output; reason: the paper fixes a RAM storing graphs as adjacency lists of half-edges with constant-time access (p. 15) but names no formal machine; unit-cost word RAM with logarithmic words is the reading; each O(·) is an explicit constant chosen after the parameters it is subscripted with
--   - encoding: decorated graphs (G, λ, R, ρ, α) over F₂^U with q colors → Decorated V H d q with labels Fin d → ZMod 2 (d = |U|), root : V → Option ℕ, colors Finset (Fin q); inputs as DecoCode edge lists; reason: Lean convention; every decorated graph is isomorphic to a code
--   - encoding: "the … folio of G can be computed/found" → the output cells hold a list of decorated-graph codes, each in the folio, such that every member of the folio (on any types) is equivalent to a listed one; reason: folios are sets of decorated graphs up to equivalence; duplicates are harmless
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 32, Lemma 26

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Decorated

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Lemma 26** (p. 32), uniform reading. One program `P` computes the `τ`-color-folio of a
decorated graph `G`; for every `τ, r_G, |U|, q` and every treewidth bound `w = f₂₆(τ, r_G, |U|, q)`
there is `c` such that on every decorated graph with these parameters and treewidth at most `w`,
`P` halts within `c · n + c` steps and outputs `C_τ(G)` up to equivalence. -/
theorem lemma_26 :
    ∃ (P : List TrulySubcubicAPSP.Instr) (b : ℕ), ∀ τ r d q w : ℕ, ∃ c : ℕ,
      ∀ (n m : ℕ) (K : DecoCode n m d q), K.toDeco.IsDecorated → K.toDeco.roots.card = r →
        K.toDeco.G.TreewidthAtMost w → ∀ W : ℕ,
        FOMCMonDep.WordSizeOK b (K.words ++ [(τ : ℤ)]) W →
        RunsWithin P W (c * n + c) (K.words ++ [(τ : ℤ)]) fun out =>
          EmitsUpToEquiv out fun F => Decorated.InColorFolio τ K.toDeco F := by sorry

end FullImmersionFPT.Main
