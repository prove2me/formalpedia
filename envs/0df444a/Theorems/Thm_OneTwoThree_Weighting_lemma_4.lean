-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_4
-- name    : OneTwoThree.Weighting.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:38.628428+00:00
-- url     : https://prove2.me/theorems/df7ed484-5818-483e-9772-6f83323a4673
-- title:
--   Lemma 4 — in the network $G_{C,F,\sigma}$ of a maximum cut there is an $s$-$t$-flow of value $|F|$
-- statement:
--   Let $G=(V,E)$ be a finite graph and let $C=(S,T)$ be a maximum cut of $G$. Let $F\subseteq E(S)\cup E(T)$ be any set of edges lying inside the two sides, and let $\sigma$ be an orientation of $F$. Let $G_{C,F,\sigma}$ be the auxiliary directed multigraph network with nodes $V\cup\{s,t\}$, the two arcs $(u,v)$, $(v,u)$ for each cut edge $\{u,v\}\in E(S,T)$, and the arcs $(s,u)$ and $(v,t)$ for each $(u,v)\in\sigma$, all of capacity $1$. Then $G_{C,F,\sigma}$ admits an (integral) $s$-$t$-flow $\varphi$ with
--   $$|\varphi|=|F|.$$
--
--   The paper quotes this lemma from Keusch (Combinatorica 2023, Lemma 2). In the proof of Lemma 3 the flow is decomposed into $|F|$ edge-disjoint $s$-$t$-paths, along which edge weights are shifted by one.
--
--   **Formalization Note** The flow is integral, i.e. $0/1$ on every arc; the page says "an $s$-$t$-flow", and the paper uses integrality immediately afterwards (p. 5). By the integrality theorem the integral and real-valued statements are equivalent. $|F|=|\sigma|$ because $\sigma$ orients each edge of $F$ exactly once.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 4, Lemma 4 (Lemma 2 in [18] = R. Keusch, Vertex-coloring graphs with 4-edge-weightings, Combinatorica 2023)

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_STFlow
import Definitions.Def_OneTwoThree_Weighting_AuxNetwork

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem lemma_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (hS : IsMaxCut G S) (σ : Finset (V × V))
    (hσ : IsSideOrientation G S σ) :
    ∃ φ : AuxArc G S σ → ℕ,
      IsSTFlow (auxTail G S σ) (auxHead G S σ) (fun _ => 1) Node.src Node.snk φ ∧
      flowValue (auxTail G S σ) (auxHead G S σ) Node.src φ = (#σ : ℤ) := by sorry

end OneTwoThree.Weighting
