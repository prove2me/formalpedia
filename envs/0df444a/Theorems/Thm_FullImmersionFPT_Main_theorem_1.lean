-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_theorem_1
-- name    : FullImmersionFPT.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:49:01.879239+00:00
-- url     : https://prove2.me/theorems/62a468c2-abe1-442e-b970-55698bb050c7
-- title:
--   Theorem 1 — full immersion testing in labeled tour graphs in f(|H|)·n⁵ time
-- statement:
--   A **labeled tour graph** is a connected 4-regular graph (loops and parallel edges allowed) whose edges carry vectors of $\mathbb F_2^d$. $H$ is a **full immersion** of $G$ if $H$ is obtained from $G$ by a sequence of shiftings (adding a vector to every edge of a cut) and splittings off of vertices (pairing the four half-edges at a vertex, not two halves of a loop or of a 2-edge cut, and merging each pair into one edge carrying the sum of the labels); isomorphisms preserve labels exactly; $|H|=|V(H)|+d'$ for $H$ labeled in $\mathbb F_2^{d'}$.
--
--   **Theorem.** There is an algorithm that tests whether an $n$-vertex labeled tour graph $G$ has a full immersion isomorphic to a labeled tour graph $H$ in time $O_{|H|}(n^5)$. Formally: there are one word-RAM program $P$, a word-size factor $b$ and a computable $f:\mathbb N\to\mathbb N$ such that for all labeled tour graphs $G$ and $H$ (any label dimensions), on the code of $(G,H)$ and at every word size $W\ge b(\lfloor\log_2(N+2)\rfloor+1)$, $P$ halts within
--   $$f(|H|)\cdot n^5+f(|H|)$$
--   steps and accepts exactly when $G$ has a full immersion isomorphic to $H$. Even for one-bit labels no polynomial-time algorithm for fixed $H$ was known before.
--
--   Differences from the source:
--   - reading: "an algorithm … in time O_{|H|}(n⁵)" → one program P of the published TrulySubcubicAPSP word RAM, a factor b and a computable f : ℕ → ℕ fixed before G and H; on the code of (G, H) and every W with FOMCMonDep.WordSizeOK b, P decides within f(|H|)·n⁵ + f(|H|) steps; reason: the title says fixed-parameter tractable and footnote 8 says "we require a computable bound"; the paper's algorithms run on a RAM with adjacency lists and constant-time access (p. 15); H is part of the input (one uniform program)
--   - encoding: labeled tour graphs G (n vertices) and H → EdgeCode n m d and EdgeCode n′ m′ d′ (edge lists with label bits), input = words of G followed by words of H; |H| = n′ + d′; reason: every labeled tour graph is isomorphic to an edge list; every edge order and orientation is allowed
--   - encoding: G labeled in F₂^d and H in F₂^{d′} → the answer requires d′ = d (CodeHasFullImmersionIso transports H's labels along the equality); reason: isomorphisms preserve labels and no change of basis or projection is allowed (p. 2)
--   - encoding: footnote 2: "we do not allow two half-edges to be paired if they are part of the same loop or 2-edge cut" → IsLegalPairing: π h ≠ mate h, and there is no S ⊆ V(G) with δ(S) = {edge of h, edge of π h}; a loop at v paired with two other edges joins them into one edge (§18.1); reason: literal encoding of the footnote; splitting off pairs half-edges
--   - encoding: "a connected 4-regular graph" → connected includes non-empty; every shifting and splitting off is applied to a labeled tour graph; reason: Lean convention as in Mathlib; the operations are defined on labeled tour graphs
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 2, Theorem 1 (restated p. 29)

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_FullImmersion

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Theorem 1** (p. 2). There are one word-RAM program `P`, a word-size factor `b` and a
computable `f : ℕ → ℕ` such that for all labeled tour graphs `G` (`n` vertices, labels in `F₂^d`)
and `H` (labels in `F₂^{d′}`), `P` on the code of `(G, H)` decides within `f(|H|) · n⁵ + f(|H|)`
steps whether `G` has a full immersion isomorphic to `H`, where `|H| = |V(H)| + d′`. -/
theorem theorem_1 :
    ∃ (P : List TrulySubcubicAPSP.Instr) (b : ℕ) (f : ℕ → ℕ), Computable f ∧
      ∀ (n m d n' m' d' : ℕ) (G : EdgeCode n m d) (K : EdgeCode n' m' d'),
        IsLabeledTourGraph G.graph G.label → IsLabeledTourGraph K.graph K.label → ∀ W : ℕ,
        FOMCMonDep.WordSizeOK b (G.words ++ K.words) W →
        FOMCMonDep.DecidesWithin P W (f (size K) * n ^ 5 + f (size K)) (G.words ++ K.words)
          (CodeHasFullImmersionIso G K) := by sorry

end FullImmersionFPT.Main
