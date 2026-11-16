-- Prove2me | Theorems.Thm_ImplicitParityWL_Supplement_theorem_10_6
-- name    : ImplicitParityWL.Supplement.theorem_10_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:32:12.90399+00:00
-- url     : https://prove2.me/theorems/6328e7ec-5c6f-4671-817b-447074cbcef5
-- title:
--   Theorem 10.6 — a witness with a one-vertex decomposition yields a contradiction tree of size $\le5|V(F)|+1$
-- statement:
--   Fix $k\ge3$, $\ell\ge1$, an implicit parity system $\mathcal I$ with coordinate set $[k]\times\mathbb F_2^\ell$, and the colored graphs $G_0,G_1$ it compiles to (§5.1). Let $F$ be a colored graph with a one-vertex tree decomposition of width at most $k$ such that
--   $$\hom(F,G_0)\ne\hom(F,G_1).$$
--   Then $\mathcal I$ has a contradiction tree with at most $5|V(F)|+1$ nodes.
--
--   Together with the converse direction (contradiction trees give witnesses), this ties the witness size of $(G_0,G_1)$ to the minimum contradiction size of $\mathcal I$, which is the route to Theorem 1.4.
--
--   **Formalization Note** $G_0,G_1$ are the published compiled graphs, $F$ is colored over their colors on a finite vertex set, and $\hom$ counts color-preserving homomorphisms. The contradiction tree is one of the parity system of $\mathcal I$, in the sense of Definition 4.1.
--
--   Differences from the source:
--   - encoding: one-vertex tree decomposition of width at most k (Definition 10.4) → HasOneVertexTD F k: a published RobersonCx tree decomposition with bags of at most k + 1 vertices, a root with empty bag, and β(t) ∖ β(s) a singleton for the neighbour s of t closer to the root; reason: in a tree the parent of a non-root node is its neighbour closer to the root
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 10.6, p.57 (standing assumptions §10, p.53)

import Mathlib
import Definitions.Def_ImplicitParityWL_CompiledGraph
import Definitions.Def_ImplicitParityWL_Supplement_Homomorphism
import Definitions.Def_ImplicitParityWL_Supplement_ContradictionTree

namespace ImplicitParityWL

namespace Supplement

/-- **Theorem 10.6** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman
Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.57): fix `k ≥ 3`, `ℓ ≥ 1`, an
implicit parity system `I` with coordinate set `[k] × 𝔽₂^ℓ` and the colored graphs `G₀`, `G₁` it compiles
to (§10, p.53). Let `F` be a colored graph with a one-vertex tree decomposition of width at most `k` such
that `hom(F, G₀) ≠ hom(F, G₁)`. Then `I` has a contradiction tree with at most `5|V(F)| + 1` nodes.

**Formalization Note** `G₀`, `G₁` are the published compiled graphs `I.graph 0`, `I.graph 1` of §5.1,
colored by `CColor`; `F` is colored over the same colors on a finite vertex type `U`. The contradiction
tree is one of the parity system `I.toParity` (Definition 4.1; children root disjoint subtrees), and its
size counts every node, including the new root. -/
theorem theorem_10_6 (k : ℕ) (hk : 3 ≤ k) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {W E : Type} [Fintype W] [Fintype E]
    (I : ImplicitSystem k ℓ W E) {U : Type} [Fintype U] (F : ColoredGraph (CColor k ℓ W E) U)
    (hF : HasOneVertexTD F k) (hhom : homCount F (I.graph 0) ≠ homCount F (I.graph 1)) :
    ∃ D : ContraTree I.toParity, D.size ≤ 5 * Fintype.card U + 1 := by sorry

end Supplement

end ImplicitParityWL
