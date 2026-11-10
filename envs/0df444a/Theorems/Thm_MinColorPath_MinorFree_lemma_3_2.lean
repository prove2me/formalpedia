-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_3_2
-- name    : MinColorPath.MinorFree.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:11:49.411204+00:00
-- url     : https://prove2.me/theorems/3273e7d7-99bd-4bcb-a8f7-f75e0f66e273
-- title:
--   Lemma 3.2 — a connected vertex set of a 0- or 1-diagram projects to a connected subgraph of G
-- statement:
--   Let $\mathcal G=(G,P,\mathrm{cl})$ be a colored graph, $G'$ a subgraph of $G$, and $\mathcal D$ the $d$-diagram of $G'$ in $\mathcal G$ for $d\in\{0,1\}$. For every $U\subseteq V(D)$ with $D[U]$ connected, the induced subgraph
--   $$G\Big[(U\cap V(G'))\cup\bigcup_{\tau\in U\cap P'}V_\tau(\mathcal G)\Big]$$
--   is connected. It transfers connectivity from the diagram back to the colored graph.
--
--   Differences from the source:
--   - encoding: D[U] connected; the conclusion's induced subgraph connected → (diagGraph cl d H).induce U is Connected; G.induce {…} is Connected (Mathlib: nonempty and preconnected); reason: with U nonempty both readings agree; U = ∅ is excluded on both sides by the same convention
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 18, Lemma 3.2

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_Diagram

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 3.2** (p. 18). Let `D` be the `d`-diagram of a subgraph `G'` of `G`, `d ∈ {0, 1}`.
For every `U ⊆ V(D)` with `D[U]` connected, the induced subgraph
`G[(U ∩ V(G')) ∪ ⋃_{τ ∈ U ∩ P'} V_τ(G)]` is connected. -/
theorem lemma_3_2 {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (hG : IsColoredGraph G P cl)
    (H : G.Subgraph) (d : ℕ) (hd : d = 0 ∨ d = 1) (U : Set (DV cl H))
    (hU : ((diagGraph cl d H).induce U).Connected) :
    (G.induce {v | (∃ h : v ∈ subVerts H, (Sum.inl ⟨v, h⟩ : DV cl H) ∈ U) ∨
      ∃ τ : ↥(diagPal cl H), (Sum.inr τ : DV cl H) ∈ U ∧ τ.1 ∈ cl v}).Connected := by sorry

end MinColorPath.MinorFree
