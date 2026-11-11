-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_5_1
-- name    : IncApproxVC.Oblivious.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:14.52625+00:00
-- url     : https://prove2.me/theorems/4b305e02-5a94-4f32-afbc-2b713a8724fb
-- title:
--   Lemma 5.1 — an $s$–$t$ cut of $G_\alpha$ of capacity $F$ has $u^+_G(S)+\alpha\,\mathrm{vol}^+_G(S)=F$, and is $s$-rooted in $G$ when $F/\alpha<m$
-- statement:
--   Let $G=(V,E,u)$ be a simple directed graph with $m$ edges and positive capacities, let $\alpha>0$, and let $G_\alpha$ be $G$ plus a new vertex $t$ and an edge $(v,t)$ of capacity $\alpha\deg^+_G(v)$ for every $v\in V$. Let $(S,T)$ be an $s$–$t$ cut of $G_\alpha$ (so $s\in S$, $t\in T$) of capacity $u^+_{G_\alpha}(S)=F$. Then
--   $$u^+_G(S)+\alpha\,\mathrm{vol}^+_G(S)=F,$$
--   and if $F/\alpha<m$, then $(S,T\cap V)$ is an $s$-rooted cut of $G$ (both sides nonempty). This identifies minimum $s$–$t$ cuts of $G_\alpha$ with minimum $s$-rooted $\alpha$-penalty cuts of $G$.
--
--   **Formalization Note.** The cut $(S,T)$ is given by $S$ with $T$ its complement; $S\cap V$ is the set of vertices $v$ with `some v ∈ S`.
--
--   Differences from the source:
--   - encoding: an s–t cut (S, T) in G_α → a vertex set S of G_α with some s ∈ S and t = none ∉ S, T its complement; S ∩ V written as the vertices v with some v ∈ S; reason: Lean representation of the cut; same cuts
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 14, Lemma 5.1

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_Cuts
import Definitions.Def_IncApproxVC_Oblivious_Flow

namespace IncApproxVC.Oblivious

/-- **Lemma 5.1** (`s–t` cuts in `G_α`), p. 14. Let `G` be a simple graph with positive edge
capacities `u`, `α > 0`, and `(S, T)` an `s–t` cut of `G_α` (`some s ∈ S`, the new vertex
`t = none ∉ S`, `T` the complement of `S`) of capacity `u⁺_{G_α}(S) = F`. Then, with `S_V` the
vertices of `G` in `S`, `u⁺_G(S_V) + α vol⁺_G(S_V) = F`, and if `F/α < m` then `(S_V, V \ S_V)` is an
`s`-rooted cut of `G`. -/
theorem lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (hG : G.Loopless)
    (u : V × V → ℝ) (hu : ∀ e ∈ G.edges, 0 < u e) (α : ℝ) (hα : 0 < α) (s : V)
    (S : Finset (Option V)) (hs : some s ∈ S) (ht : none ∉ S) (F : ℝ)
    (hF : (G.alphaNet u α).capOut S = F) :
    G.capOutG u (Finset.univ.filter fun v => some v ∈ S) +
        α * (G.vol (Finset.univ.filter fun v => some v ∈ S) : ℝ) = F ∧
      (F / α < (G.numEdges : ℝ) →
        s ∈ (Finset.univ.filter fun v => some v ∈ S) ∧
          Digraph.IsEdgeCut (Finset.univ.filter fun v => some v ∈ S)
            (Finset.univ.filter fun v => some v ∈ S)ᶜ) := by sorry

end IncApproxVC.Oblivious
