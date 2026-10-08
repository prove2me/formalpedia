-- Prove2me | Theorems.Thm_HararySachs_Hyper_lemma_9
-- name    : HararySachs.Hyper.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:30.441868+00:00
-- url     : https://prove2.me/theorems/c18f7d22-b6d9-47d8-b033-2b5d3f59505e
-- title:
--   Lemma 9 — an Euler rooting determines a connected Veblen hypergraph
-- statement:
--   Let $S$ be a $k$-uniform multi-hypergraph, with $k\ge2$, and let $R$ be a rooting of its edge multiset. If the rooted multi-digraph $D_R$ is Eulerian, then $S$ is connected and Veblen. More precisely, for each covered vertex $v$,
--
--   $$\deg_S(v)=k\,\#\{i:\text{the root of the }i\text{th edge is }v\}.$$
--
--   The edge multiset of $S$ is determined by $R$, which accounts for the paper's assertion of precisely one labeled Veblen hypergraph. This fact identifies which rooted operators contribute to the trace.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 8, Lemma 9 and its displayed degree calculation

import Mathlib
import Definitions.Def_HararySachs_Hyper_Veblen

namespace HararySachs.Hyper

theorem lemma_9 {n k : ℕ} (hk : 2 ≤ k) (S : MultiGraph n)
    (hS : IsUniform S k)
    (R : Fin S.card → Fin n × Finset (Fin n))
    (hR : IsEulerRooting S R) :
    IsVeblen S k ∧ IsConnected S ∧
      ∀ v ∈ covered S,
        vertexDegree S v = k *
          (Finset.univ.filter (fun i => (R i).1 = v)).card := by sorry

end HararySachs.Hyper
