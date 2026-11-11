-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_proposition_24
-- name    : FullImmersionFPT.Main.proposition_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:49:20.421617+00:00
-- url     : https://prove2.me/theorems/9570e0e0-be8f-4992-9abe-45a26ccb9c61
-- title:
--   Proposition 24 — the τ-color-folio of a 4-edge-connected decorated graph in O(n⁵) time
-- statement:
--   For every 4-edge-connected decorated graph $\mathcal G$ with $r_G$ roots (labels in $\mathbb F_2^U$, colors in $[q]$) and every $\tau\in\mathbb N$, the $\tau$-color-folio $C_\tau(\mathcal G)$ — the decorated graphs with at most $\tau$ vertices, each edge having at most one half-edge colored and by a single color, that $\mathcal G$ fully immerses, up to equivalence — can be computed in time
--   $$O_{\tau,r_G,|U|,q}(n^5).$$
--   Formally: one program $P$ (input: the code of $\mathcal G$ and $\tau$) and for all $\tau,r_G,|U|,q$ a constant $c$ with $P$ outputting $C_\tau(\mathcal G)$ within $c\,n^5+c$ steps. It solves the 4-edge-connected case of the main theorem.
--
--   Differences from the source:
--   - reading: "we can find/compute/test … in time O_{τ,r_G,|U|,q}(n⁵)" → one program P of the published TrulySubcubicAPSP word RAM and a word-size factor b, fixed before every input, uniform in τ, r_G, |U|, q (input: the code of G followed by τ), with c chosen after them; on every input and every word size W ≥ b(⌊log₂(N+2)⌋+1) (FOMCMonDep.WordSizeOK, N = input length plus largest absolute entry) P halts within the explicit bound with a correct output; reason: the paper fixes a RAM storing graphs as adjacency lists of half-edges with constant-time access (p. 15) but names no formal machine; unit-cost word RAM with logarithmic words is the reading; each O(·) is an explicit constant chosen after the parameters it is subscripted with
--   - encoding: decorated graphs (G, λ, R, ρ, α) over F₂^U with q colors → Decorated V H d q with labels Fin d → ZMod 2 (d = |U|), root : V → Option ℕ, colors Finset (Fin q); inputs as DecoCode edge lists; reason: Lean convention; every decorated graph is isomorphic to a code
--   - encoding: "the … folio of G can be computed/found" → the output cells hold a list of decorated-graph codes, each in the folio, such that every member of the folio (on any types) is equivalent to a listed one; reason: folios are sets of decorated graphs up to equivalence; duplicates are harmless
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 31, Proposition 24

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Decorated

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Proposition 24** (p. 31). One program `P` computes, for every 4-edge-connected decorated graph
`G` with `r_G` roots and every `τ ∈ ℕ`, the `τ`-color-folio of `G` (up to equivalence) within
`c · n⁵ + c` steps, `c` depending only on `τ, r_G, |U|, q`. -/
theorem proposition_24 :
    ∃ (P : List TrulySubcubicAPSP.Instr) (b : ℕ), ∀ τ r d q : ℕ, ∃ c : ℕ,
      ∀ (n m : ℕ) (K : DecoCode n m d q), K.toDeco.IsDecorated →
        K.toDeco.G.IsKEdgeConnected 4 → K.toDeco.roots.card = r → ∀ W : ℕ,
        FOMCMonDep.WordSizeOK b (K.words ++ [(τ : ℤ)]) W →
        RunsWithin P W (c * n ^ 5 + c) (K.words ++ [(τ : ℤ)]) fun out =>
          EmitsUpToEquiv out fun F => Decorated.InColorFolio τ K.toDeco F := by sorry

end FullImmersionFPT.Main
