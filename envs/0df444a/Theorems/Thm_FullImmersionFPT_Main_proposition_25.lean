-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_proposition_25
-- name    : FullImmersionFPT.Main.proposition_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:49:02.237118+00:00
-- url     : https://prove2.me/theorems/facb026c-2a7d-458e-b23c-854031a9d40e
-- title:
--   Proposition 25 — an irrelevant vertex for the τ-color-folio at large treewidth, found in O(n⁴) time
-- statement:
--   There is a function $f_{25}:\mathbb N^4\to\mathbb N$ such that the following holds. Let $\mathcal G=(G,\lambda,R_G,\rho_G,\alpha_G)$ be a 4-edge-connected decorated graph (labels in $\mathbb F_2^U$, colors in $[q]$), let $\tau\in\mathbb N$ and $r_G:=|R_G|$, and suppose $G$ has treewidth at least $f_{25}(\tau,r_G,|U|,q)$. Then there is a non-root vertex $v$ such that for each of the three decorated graphs $\mathcal G'$ obtained by splitting off at $v$,
--   $$\mathcal F\in C_\tau(\mathcal G)\iff\mathcal F\in C_\tau(\mathcal G')\quad\text{for every decorated graph }\mathcal F.$$
--   Furthermore such a vertex can be found in time $O_{\tau,r_G,|U|,q}(n^4)$, $n=|V(G)|$: one program $P$ (input: the code of $\mathcal G$ and $\tau$) and, for all $\tau,r_G,|U|,q$, a constant $c$ such that $P$ outputs such a vertex within $c\,n^4+c$ steps. Repeated $n$ times, this reduces Proposition 24 to bounded treewidth.
--
--   Differences from the source:
--   - reading: "there exists a vertex v ∈ V(G) such that for any of the three decorated graphs G′ obtained from splitting off at v" → v is a non-root vertex, and the equivalence holds for every pairing π of the half-edges at v that is legal by footnote 2 (Decorated.IsFolioIrrelevant); reason: §18.1 defines splitting off only at non-root vertices; in a 4-edge-connected graph with at least two vertices there are no loops or 2-edge cuts, so all three pairings are legal
--   - reading: "we can find/compute/test … in time O_{τ,r_G,|U|,q}(n⁴)" → one program P of the published TrulySubcubicAPSP word RAM and a word-size factor b, fixed before every input, uniform in τ, r_G, |U|, q (input: the code of G followed by τ), with c chosen after τ, r_G, |U|, q; on every input and every word size W ≥ b(⌊log₂(N+2)⌋+1) (FOMCMonDep.WordSizeOK, N = input length plus largest absolute entry) P halts within the explicit bound with a correct output; reason: the paper fixes a RAM storing graphs as adjacency lists of half-edges with constant-time access (p. 15) but names no formal machine; unit-cost word RAM with logarithmic words is the reading; each O(·) is an explicit constant chosen after the parameters it is subscripted with
--   - encoding: decorated graphs (G, λ, R, ρ, α) over F₂^U with q colors → Decorated V H d q with labels Fin d → ZMod 2 (d = |U|), root : V → Option ℕ, colors Finset (Fin q); inputs as DecoCode edge lists; reason: Lean convention; every decorated graph is isomorphic to a code
--   - encoding: "F is in the τ-color-folio of G iff it is in that of G′" → InColorFolio τ G F ↔ InColorFolio τ G′ F for every decorated graph F on any types; reason: membership is invariant under equivalence, so this is equality of the folios as sets of classes
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 32, Proposition 25

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Decorated

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Proposition 25** (p. 32). There is `f₂₅ : ℕ⁴ → ℕ` such that: if `G` is a 4-edge-connected
decorated graph with `r_G` roots, labels in `F₂^U` (`|U| = d`), colors in `[q]`, and treewidth at least
`f₂₅(τ, r_G, |U|, q)`, then some non-root vertex `v` is irrelevant for the `τ`-color-folio (for each of
the three ways of splitting off at `v`, `C_τ(G′) = C_τ(G)`). Furthermore one program `P` finds such
a vertex within `c · n⁴ + c` steps, `c` depending only on `τ, r_G, |U|, q`. -/
theorem proposition_25 :
    ∃ f25 : ℕ → ℕ → ℕ → ℕ → ℕ,
      (∀ (τ d q : ℕ) (V H : Type) (D : Decorated V H d q), D.IsDecorated →
        D.G.IsKEdgeConnected 4 → D.G.TreewidthAtLeast (f25 τ D.roots.card d q) →
        ∃ v, D.IsFolioIrrelevant τ v) ∧
      ∃ (P : List TrulySubcubicAPSP.Instr) (b : ℕ), ∀ τ r d q : ℕ, ∃ c : ℕ,
        ∀ (n m : ℕ) (K : DecoCode n m d q), K.toDeco.IsDecorated →
          K.toDeco.G.IsKEdgeConnected 4 → K.toDeco.roots.card = r →
          K.toDeco.G.TreewidthAtLeast (f25 τ r d q) → ∀ W : ℕ,
          FOMCMonDep.WordSizeOK b (K.words ++ [(τ : ℤ)]) W →
          RunsWithin P W (c * n ^ 4 + c) (K.words ++ [(τ : ℤ)]) fun out =>
            ∃ v : Fin n, K.toDeco.IsFolioIrrelevant τ v ∧
              FOMCMonDep.Emits out [((v : ℕ) : ℤ)] := by sorry

end FullImmersionFPT.Main
