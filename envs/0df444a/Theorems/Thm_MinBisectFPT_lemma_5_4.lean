-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_5_4
-- name    : MinBisectFPT.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:57.86554+00:00
-- url     : https://prove2.me/theorems/1c6eb85a-0037-44d8-87c0-553c28641bec
-- title:
--   Lemma 5.4 — at the end of the loop $\beta$ is $(3k,k)$-edge-unbreakable
-- statement:
--   Consider a call $\mathrm{Decompose}(D)$ of Algorithm 2 past Line 3, on a connected graph $G$ with $k\ge1$, with $H=H_D$, $|Z|=2k+1$ and $Z\subseteq\beta\subseteq V(H)$.
--   If no set under consideration has $\mathrm{ex}(R)\ge1$, then $\beta$ is $(3k,k)$-edge-unbreakable in $H$.
--
--   Differences from the source:
--   - generalization: the current bag $\beta$ in a call of Algorithm 2 → any $\beta$ with the listed invariants; reason: the loop maintains them, so every state of the loop is an instance
--   - encoding: graphs $G_t$, $H_D$ on their own vertex sets → the same graphs on the ambient `Fin n`, with the other vertices isolated and every $X\subseteq V(H)$ written `X ⊆ VH`; reason: isolated ambient vertices change no cut and no neighbourhood
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.4, p.19

import Mathlib
import Definitions.Def_MinBisectFPT_IsDecomposeRun
import Definitions.Def_MinBisectFPT_IsUnbreakableTD

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 5.4.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.4, p.19: "When the loop of Line 4 ends, β is (3k, k)-edge-unbreakable
in H." -/
theorem lemma_5_4 {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (k : ℕ) (hk : 1 ≤ k)
    (D Z β : Finset (Fin n)) (hsetup : IsCallSetup G k D Z) (hβ : β ⊆ callVerts G D) (hI1 : Z ⊆ β)
    (hend : LoopEnded (callGraph G D) Z β k) :
    IsEdgeUnbreakable (callGraph G D) (callVerts G D) β (3 * k) k := by sorry

end MinBisectFPT
