-- Prove2me | Theorems.Thm_NicerEars_TJoin_lemma_5
-- name    : NicerEars.TJoin.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:38.750988+00:00
-- url     : https://prove2.me/theorems/33772092-14b7-4ce5-ad09-42d2b9f2987a
-- title:
--   Lemma 5 — local T-join and connected-T-join bounds for a pendant ear
-- statement:
--   Let $G$ be a 2-edge-connected graph with an ear-decomposition, $T\subseteq V(G)$ with $|T|$ even, and $P$ a pendant ear. Then there exist $F,F'\subseteq E(P)$ (with $F'$ a multi-subset, i.e. in $2G$) and $S,S'\subseteq V(G)\setminus\mathrm{in}(P)$, with $|S|$ and $|S'|$ even, such that:
--
--   1. $|F|\le\tfrac12|\mathrm{in}(P)|+\tfrac12\varphi(P)$, and $F\cup J$ is a $T$-join in $G$ for every $S$-join $J$ in $G-\mathrm{in}(P)$;
--   2. $|F'|\le\tfrac32|\mathrm{in}(P)|+\tfrac12\varphi(P)+\gamma(P)-1$, and $F'\cup J'$ is a connected-$T$-join of $G$ for every connected-$S'$-join $J'$ of $G-\mathrm{in}(P)$.
--
--   Here $\varphi(P)=1$ if $P$ has an even number of edges and $0$ otherwise, and $\gamma(P)=1$ if $P$ is short (2 or 3 edges) with $\mathrm{in}(P)\cap T=\emptyset$, $0$ otherwise. The lemma is the inductive step behind Proposition 6, Proposition 8 and Theorem 24.
--
--   **Formalization Note.** The running time $O(|\mathrm{in}(P)|)$ is not formalized. $G-\mathrm{in}(P)$ is $G$ with the internal vertices of $P$ deleted: a (multi-)edge set of it is one whose edges have no end in $\mathrm{in}(P)$, and connectivity of $J'$ is taken on the vertex set $V(G)\setminus\mathrm{in}(P)$. The sets $F,F',S,S'$ are chosen before the joins $J,J'$. The evenness of $|S|$ and $|S'|$ is explicit: the page speaks of $S$-joins, which it defines only for sets of even size (p. 2); without it an odd $S$ would admit no $S$-join and make the lemma vacuous.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 7, Lemma 5

import Mathlib
import Definitions.Def_NicerEars_TJoin_Ears

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Lemma 5 (p. 7), existence part. `G` has the ear-decomposition `D`, `|T|` is even and `P = Pᵢ`
is a pendant ear. There are `F ⊆ E(P)`, a multi-subset `F'` of `E(P)` (a subset of 2G) and
`S, S' ⊆ V(G) ∖ in(P)`, of even size (an S-join is only defined for `|S|` even, p. 2), such that
(a) `|F| ≤ ½|in(P)| + ½ϕ(P)` and `F ∪ J` is a T-join in `G` for every S-join `J` in `G − in(P)`;
(b) `|F'| ≤ 3/2|in(P)| + ½ϕ(P) + γ(P) − 1` and `F' ∪ J'` is a connected-T-join of `G` for every
connected-S'-join `J'` of `G − in(P)`.
An edge set of `G − in(P)` is an edge set of `G` none of whose edges has an end in `in(P)`. -/
theorem lemma_5 (G : Graph V E) (hG : G.IsTwoEdgeConnected) (D : EarDecomposition G)
    (T : Finset V) (hT : Even #T) (i : Fin D.k) (hP : D.IsPendant i) :
    ∃ (F : Finset E) (F' : Finset (E × Fin 2)) (S S' : Finset V),
      F ⊆ (D.ear i).edges ∧ F'.image Prod.fst ⊆ (D.ear i).edges ∧
      Disjoint S (D.ear i).inner ∧ Disjoint S' (D.ear i).inner ∧ Even #S ∧ Even #S' ∧
      -- (a)
      ((#F : ℝ) ≤ 1 / 2 * #(D.ear i).inner + 1 / 2 * (D.ear i).phiEar ∧
        ∀ J : Finset E, (∀ e ∈ J, ∀ u ∈ G.ends e, u ∉ (D.ear i).inner) → G.IsTJoin S J →
          G.IsTJoin T (F ∪ J)) ∧
      -- (b)
      ((#F' : ℝ) ≤ 3 / 2 * #(D.ear i).inner + 1 / 2 * (D.ear i).phiEar + (D.ear i).gamma T - 1 ∧
        ∀ J' : Finset (E × Fin 2), (∀ e ∈ J', ∀ u ∈ G.ends e.1, u ∉ (D.ear i).inner) →
          G.double.IsTJoin S' J' →
          ((G.double.spanGraph J').induce {u | u ∉ (D.ear i).inner}).Connected →
          G.IsConnectedTJoin T (F' ∪ J')) := by sorry

end NicerEars.TJoin
