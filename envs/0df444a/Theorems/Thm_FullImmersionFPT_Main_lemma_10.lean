-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_lemma_10
-- name    : FullImmersionFPT.Main.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:48:55.296598+00:00
-- url     : https://prove2.me/theorems/9f234c88-dc14-4646-990a-4f53ecac8546
-- title:
--   Lemma 10 — the value of a flooding is at most the value of a certificate
-- statement:
--   Let $\mathcal G=(G,\Sigma,F,t)$ be a free graph: $G$ Eulerian, $\Sigma$ and $F$ sets of edges, $t$ a vertex. For every flooding $\mathcal C$ (a collection of $\deg(t)/2$ $t$-circuits partitioning $E(G)$) and every certificate $(X,\Sigma')$ ($t\in X\subseteq V(G)$, $\Sigma'$ a shifting of $\Sigma$),
--   $$\mathrm{value}(\mathcal C)\;\le\;\mathrm{value}(X,\Sigma') = |E_{F,\Sigma'}(X)|+\tfrac12|\delta(X)|-\mathrm{odd}_{\Sigma'}(G-X).$$
--   Equivalently, the maximum value of a flooding is at most the minimum value of a certificate. This is the easy direction of the min-max Theorem 3.
--
--   Differences from the source:
--   - encoding: the maximum value of a flooding is at most the minimum value of a certificate → every flooding has value at most the value of every certificate; reason: floodings and certificates exist (G is Eulerian, (V(G), Σ) is a certificate) and are finitely many, so the two statements are equivalent
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
--   - encoding: value(X, Σ′) = |E_{F,Σ′}(X)| + |δ(X)|/2 − odd_{Σ′}(G − X) → certValue in ℤ with (|δ(X)| : ℤ) / 2; reason: |δ(X)| is even in an Eulerian graph, so the division is exact; ℤ avoids truncated subtraction
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 14, Lemma 10

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Flooding

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Lemma 10** (p. 14). For any free graph `Γ = (G, Σ, F, t)`, the value of every flooding is at
most the value of every certificate; equivalently, the maximum value of a flooding is at most the
minimum value of a certificate. -/
theorem lemma_10 {V H : Type} (Γ : FreeGraph V H) (hΓ : Γ.IsFree) (C : List (List H))
    (hC : Γ.IsFlooding C) (X : Finset V) (S' : Finset (Sym2 H)) (hX : Γ.IsCertificate X S') :
    (Γ.floodValue C : ℤ) ≤ Γ.certValue X S' := by sorry

end FullImmersionFPT.Main
