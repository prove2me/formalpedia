-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_5_1
-- name    : MinColorPath.MinorFree.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:13:15.489727+00:00
-- url     : https://prove2.me/theorems/edac8a90-a96c-47a6-b36f-7188b0f1742a
-- title:
--   Lemma 5.1 — rounding the separator LP: an (A, B)-separator of cover number ≤ (2cdeg+3)·ℓ
-- statement:
--   Let $\mathcal G$ be a clean colored graph, $G'$ a subgraph of $G$, $\mathcal D=(D,P',\mathrm{cl}')$ the diagram of $G'$ in $\mathcal G$, $\mathcal F$ its star family and $A,B\subseteq V(D)$. If LP 1 for $(A,B,D)$ has optimal value at most $\ell$, then some $(A,B)$-separator $S$ of $D$ satisfies
--   $$\mathrm{cov}_{\mathcal F}(S)\le(2\,\mathrm{cdeg}(\mathcal G)+3)\cdot\ell.$$
--   It is the rounding step that turns the fractional separator bound used in Lemma 5.2 into an integral one.
--
--   Differences from the source:
--   - encoding: LP 1 has optimal objective value at most ℓ → LPAtMost cl H A B ℓ: a feasible x ≥ 0 indexed by P′ with ∑ x ≤ ℓ; reason: finitely many constraints and a nonnegative objective: the optimum is attained when the LP is feasible and is +∞ otherwise
--   - encoding: cov_F(S) ≤ (2 cdeg(G) + 3) · ℓ → ∃ R ⊆ P′ with S ⊆ F_R and |R| ≤ (2 cdeg + 3) ℓ (reals); reason: cov_F(S) is the least such |R|
--   - reading: an (A, B)-separator S in D → IsSeparator: every path of D from a vertex of A to a vertex of B contains a vertex of S; reason: the paper uses the notion without a definition; this is the standard one, and constraining all A–B paths or only those internally disjoint from A ∪ B gives the same sets
--   - encoding: G clean (p. 19): {v : cl(v) = ∅} = {s, t} → IsClean cl s t with explicit terminals s t; reason: cleanliness is defined relative to the terminals
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 26, Lemma 5.1

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_StarFamily

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 5.1** (p. 26). Let `G` be clean, `G'` a subgraph, `D` the diagram of `G'` in `G` and
`A, B ⊆ V(D)`. If LP 1 for `(A, B, D)` has optimal value at most `ℓ`, then some
`(A, B)`-separator `S` of `D` has `cov_F(S) ≤ (2 cdeg(G) + 3) · ℓ`. -/
theorem lemma_5_1 {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (hG : IsColoredGraph G P cl)
    (s t : V) (hclean : IsClean cl s t) (H : G.Subgraph)
    (A B : Finset (DV cl H)) (ℓ : ℝ) (hLP : LPAtMost cl H A B ℓ) :
    ∃ S : Finset (DV cl H), IsSeparator (diagGraph cl 1 H) A B S ∧
      ∃ R : Finset ↥(diagPal cl H), S ⊆ starUnion cl H R ∧
        (R.card : ℝ) ≤ (2 * (cdeg P cl : ℝ) + 3) * ℓ := by sorry

end MinColorPath.MinorFree
