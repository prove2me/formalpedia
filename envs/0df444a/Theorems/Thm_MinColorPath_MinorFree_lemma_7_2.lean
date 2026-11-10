-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_7_2
-- name    : MinColorPath.MinorFree.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:13:48.69121+00:00
-- url     : https://prove2.me/theorems/612ff3e2-daab-4787-bff9-92381ccb332e
-- title:
--   Lemma 7.2 — strong base closure: components of D − A⁺ contain colors and are O(|cl′(A⁺)|(cdeg+1) + |A ∩ V₀(π)|) many
-- statement:
--   Let $\mathcal G$ be a semi-clean colored graph with terminals $s,t$, $\pi$ a min-color $(s,t)$-path, $\mathcal D$ its $d$-diagram ($d\in\mathbb N_0$), $A\subseteq V(D)$ nonempty and $A^+$ its strong base closure. Then (i) every connected component of $D-A^+$ contains a vertex of $P'$, and (ii) for an absolute constant $K$,
--   $$\#\{\text{components of } D-A^+\}\le K\big(|\mathrm{cl}'(A^+)|\,(\mathrm{cdeg}(\mathcal G)+1)+|A\cap V(\pi)\cap V_0(\mathcal G)|\big).$$
--   It bounds how many pieces a bag splits the diagram into, a step towards the crossing-number bound of Theorem 7.1.
--
--   Differences from the source:
--   - reading: the standing context of §7 (p. 41): G = (G, P, cl) is a semi-clean colored graph with s, t ∈ V(G) → hypotheses IsColoredGraph G P cl and IsSemiClean G cl s t; reason: §7 fixes this context once at its top (p. 41); the lemma's sentence omits it
--   - reading: O(|cl′(A+)|·(cdeg(G)+1) + |A ∩ (V(π) ∩ V0(G))|) → K · (…) for one constant K : ℕ quantified before every type, graph and set; reason: the lemma does not involve h; the bracket is ≥ 1 for nonempty A in a nontrivial case, so a multiplicative constant is the meaning of O(·)
--   - reading: π a min-color path in G → π a min-color (s, t)-path for the context's terminals; reason: the §7 context fixes s, t
--   - encoding: D − A+ and its connected components → the induced graph of the diagram on the complement of A⁺, its ConnectedComponent type, counted with Nat.card; a color vertex is Sum.inr; reason: standard
--   - encoding: a min-color (s, t)-path π → IsMinColorPath cl π: π.IsPath and its colored length (as ℕ∞) equals cdist G cl s t; reason: the definition of p. 17
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), pp. 41–42, Lemma 7.2

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_Closures

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 7.2** (pp. 41–42). There is an absolute constant `K` such that: for a semi-clean
colored graph `G`, a min-color `(s, t)`-path `π`, its `d`-diagram `D` and a nonempty `A ⊆ V(D)`
with strong base closure `A⁺`, (i) every connected component of `D − A⁺` contains a color vertex,
and (ii) `D − A⁺` has at most `K (|cl'(A⁺)| (cdeg(G) + 1) + |A ∩ V(π) ∩ V_0(G)|)` components. -/
theorem lemma_7_2 :
    ∃ K : ℕ, ∀ (V C : Type) [Fintype V] [DecidableEq V] [DecidableEq C]
      (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C), IsColoredGraph G P cl →
      ∀ s t : V, IsSemiClean G cl s t →
      ∀ (π : G.Walk s t), IsMinColorPath cl π → ∀ (d : ℕ) (A : Finset (DV cl π.toSubgraph)),
        A.Nonempty →
        (∀ c : ((pathDiag cl d π).induce
              {y | y ∉ strongBaseClosure cl π.toSubgraph A}).ConnectedComponent,
            ∃ y : ↥({y | y ∉ strongBaseClosure cl π.toSubgraph A} : Set (DV cl π.toSubgraph)),
              ((pathDiag cl d π).induce
                {y | y ∉ strongBaseClosure cl π.toSubgraph A}).connectedComponentMk y = c ∧
              y.1.isRight = true) ∧
        Nat.card ((pathDiag cl d π).induce
            {y | y ∉ strongBaseClosure cl π.toSubgraph A}).ConnectedComponent ≤
          K * ((colSet (diagCl cl π.toSubgraph) (strongBaseClosure cl π.toSubgraph A)).card *
              (cdeg P cl + 1) +
            uncoloredBaseCount cl π.toSubgraph A) := by sorry

end MinColorPath.MinorFree
