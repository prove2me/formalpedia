-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_lemma_33
-- name    : FullImmersionFPT.Main.lemma_33
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:48:45.300509+00:00
-- url     : https://prove2.me/theorems/a1c81f5c-dcfe-4808-84c8-47d465ab8959
-- title:
--   Lemma 33 — a small signature-separating cut in a 4-edge-connected free graph
-- statement:
--   Let $(G,\Sigma,F,t)$ be a 4-edge-connected Eulerian free graph whose flooding number satisfies $\nu(G,\Sigma,F,t)\le\ell$. Then there are a shifting $\Sigma'$ of $\Sigma$ and a set of vertices $X$ containing $t$ such that
--   $$|\delta(X)|\le 4\ell\qquad\text{and}\qquad |E_{F,\Sigma'}(X)|\le\ell,$$
--   that is, at most $\ell$ edges with both ends in $X$ are free or in $\Sigma'$. Further, every certificate $(X,\Sigma')$ of value at most $\ell$ has these two properties; in particular the certificate of value at most $\ell$ returned by the algorithm of Theorem 3 does. It is the step of Part III that turns a small flooding number into a small cut.
--
--   Differences from the source:
--   - encoding: ν(G, Σ, F, t) ⩽ ℓ → every flooding has value at most ℓ (ℓ : ℕ); reason: ν is the maximum value of a flooding, and floodings exist; ν ≥ 0
--   - generalization: "Further, (X, Σ′) are given by the certificate of value at most ℓ returned by the algorithm of Theorem 3" → every certificate (X, Σ′) of value at most ℓ satisfies 1 and 2; reason: the returned certificate has value ν ≤ ℓ, so this specializes to it; the algorithm is not a named object of the statement
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
--   - encoding: value(X, Σ′) = |E_{F,Σ′}(X)| + |δ(X)|/2 − odd_{Σ′}(G − X) → certValue in ℤ with (|δ(X)| : ℤ) / 2; reason: |δ(X)| is even in an Eulerian graph, so the division is exact; ℤ avoids truncated subtraction
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 44, Lemma 33

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Flooding

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Lemma 33** (p. 44, small signature-separating cut). Let `(G, Σ, F, t)` be a 4-edge-connected
Eulerian free graph with `ν(G, Σ, F, t) ≤ ℓ`. Then there are a shifting `Σ′` of `Σ` and a vertex
set `X ∋ t` with `|δ(X)| ≤ 4ℓ` and `|E_{F,Σ′}(X)| ≤ ℓ`; further, every certificate `(X, Σ′)` of value
at most `ℓ` (in particular the one returned by the algorithm of Theorem 3) has these two
properties. -/
theorem lemma_33 {V H : Type} (Γ : FreeGraph V H) (hΓ : Γ.IsFree) (h4 : Γ.G.IsKEdgeConnected 4)
    (ℓ : ℕ) (hν : ∀ C, Γ.IsFlooding C → Γ.floodValue C ≤ ℓ) :
    (∃ (X : Finset V) (S' : Finset (Sym2 H)), Γ.IsCertificate X S' ∧
        (Γ.G.cut X).card ≤ 4 * ℓ ∧ (Γ.EFS X S').card ≤ ℓ) ∧
      ∀ (X : Finset V) (S' : Finset (Sym2 H)), Γ.IsCertificate X S' → Γ.certValue X S' ≤ ℓ →
        (Γ.G.cut X).card ≤ 4 * ℓ ∧ (Γ.EFS X S').card ≤ ℓ := by sorry

end FullImmersionFPT.Main
