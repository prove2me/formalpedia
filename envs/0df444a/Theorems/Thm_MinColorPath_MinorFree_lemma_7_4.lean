-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_7_4
-- name    : MinColorPath.MinorFree.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:13:48.894369+00:00
-- url     : https://prove2.me/theorems/62093785-290a-4fe4-b589-fb531c2a9912
-- title:
--   Lemma 7.4 — rerouting through V_τ across seven alternating vertices strictly decreases the covering number
-- statement:
--   Let $\pi$ be a path in the semi-clean colored graph $\mathcal G$ and $\tau\in P$. Suppose $v_1,\dots,v_7\in V(\pi)$ appear in this order along $\pi$ with $v_1,v_3,v_5,v_7\in V_\tau(\mathcal G)$ and $v_2,v_4,v_6\notin V_\mu(\mathcal G)$ for every $\mu\in N_{\Gamma_{\mathcal G}}[\tau]$. Let $\tilde\pi$ be a path in $G[V_\tau(\mathcal G)]$ from $v_1$ to $v_7$. Then the walk obtained from $\pi$ by replacing its $v_1$–$v_7$ subpath with $\tilde\pi$ has
--   $$\text{covering number} < \text{covering number of } \pi.$$
--   It is why a min-color path of least covering number exists with the properties used in Theorem 7.1.
--
--   Differences from the source:
--   - reading: the standing context of §7 (p. 41): G = (G, P, cl) is a semi-clean colored graph with s, t ∈ V(G) → hypotheses IsColoredGraph G P cl and IsSemiClean G cl s t; reason: §7 fixes this context once at its top (p. 41); the lemma's sentence omits it
--   - encoding: v1, …, v7 ∈ V(π) sorted along π → positions idx : Fin 7 → Fin π.support.length, strictly increasing; v_{k+1} = π.support.get (idx k); reason: 0-based positions along the path
--   - encoding: π̃ a path in G[Vτ(G)] connecting v1 and v7 → π′ : G.Walk v1 v7 with IsPath and τ ∈ cl v for every vertex; reason: a path of an induced subgraph is a path of G inside the vertex set
--   - encoding: the walk obtained from π by replacing π′ with π̃ → the vertex list π.support.take (idx 0) ++ π̃.support ++ π.support.drop (idx 6 + 1); reason: the replaced walk as a sequence of vertices
--   - encoding: v2, v4, v6 ∉ Vµ(G) for any µ ∈ N_ΓG[τ] → ∀ μ, (μ = τ ∨ Γ.Adj τ μ) → μ ∉ cl v; reason: the closed neighbourhood in Γ
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 44, Lemma 7.4

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_Closures

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 7.4** (p. 44). Let `π` be a path of the semi-clean colored graph `G`, `τ ∈ P`, and
`v_1, …, v_7` vertices of `π` in this order along `π` with `v_1, v_3, v_5, v_7 ∈ V_τ(G)` and
`v_2, v_4, v_6 ∉ V_μ(G)` for every `μ ∈ N_{Γ_G}[τ]`. If `π̃` is a path of `G[V_τ(G)]` from `v_1`
to `v_7`, the walk obtained from `π` by replacing its `v_1`–`v_7` subpath with `π̃` has strictly
smaller covering number than `π`. (Positions are 0-based: `v_{k+1}` is at position `idx k`.) -/
theorem lemma_7_4 {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (hG : IsColoredGraph G P cl)
    (s t : V) (hsc : IsSemiClean G cl s t) {a b : V} (π : G.Walk a b) (hπ : π.IsPath)
    (τ : C) (hτ : τ ∈ P) (idx : Fin 7 → Fin π.support.length) (hidx : StrictMono idx)
    (hodd : ∀ k ∈ ({0, 2, 4, 6} : Finset (Fin 7)), τ ∈ cl (π.support.get (idx k)))
    (heven : ∀ k ∈ ({1, 3, 5} : Finset (Fin 7)), ∀ μ : C,
      (μ = τ ∨ (colorGraph cl).Adj τ μ) → μ ∉ cl (π.support.get (idx k)))
    (π' : G.Walk (π.support.get (idx 0)) (π.support.get (idx 6))) (hπ' : π'.IsPath)
    (hπ'τ : ∀ v ∈ π'.support, τ ∈ cl v) :
    coveringNumber P cl
        (π.support.take (idx 0).val ++ π'.support ++ π.support.drop ((idx 6).val + 1)) <
      coveringNumber P cl π.support := by sorry

end MinColorPath.MinorFree
