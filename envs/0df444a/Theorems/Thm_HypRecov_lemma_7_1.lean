-- Prove2me | Theorems.Thm_HypRecov_lemma_7_1
-- name    : HypRecov.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:37:18.78437+00:00
-- url     : https://prove2.me/theorems/ee5bbab9-dc73-483d-93c5-58067e3e3479
-- title:
--   Lemma 7.1 — completing a recovered edge family
-- statement:
--   Let $H$ be a finite simple hypergraph on $V$, $k\ge 0$, and $F$ a family of edges with $\mathcal B_k(H)\subseteq F\subseteq E(H)$. Let $\mathcal T$ be a family of two-vertex sets whose graph has exactly the connected components of $H\setminus F$ (for instance a spanning tree of each component). Let $\widehat H$ consist of the sets of $\mathcal T$ with weight $k$ and the edges of $F$ with weight $1$. Then for every $S\subseteq V$,
--   $$\min\{\mathrm{cut}_H(S),k\}=\min\{\mathrm{cut}_{\widehat H}(S),k\}.$$
--
--   The unrecovered edges matter only through their components, so a compact weighted representation preserves every cut below $k$.
--
--   Differences from the source:
--   - generalization: "In each C_i, choose an arbitrary spanning tree on its vertices" → any family of two-vertex sets whose graph has exactly the components of H ∖ F; reason: the union of spanning trees of the components is such a family (paper.md decision 11)
--   - generalization: H simple, unweighted, r-uniform → any finite family of vertex sets; reason: the proof does not use uniformity; the r-uniform case is an instance
--   - encoding: connected components of H ∖ F; Ĥ → reachability in the two-section; a weighted list; reason: Lean convention
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 7.1, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_cutW
import Definitions.Def_HypRecov_twoSection

namespace HypRecov

/-- **Lemma 7.1 (Completing a recovered edge family).** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 7.1, p.18
(PDF p.19): "Suppose a family F of original edges satisfies ℬ_k(H) ⊆ F ⊆ E(H). Let C_1, . . . , C_s be
the connected components of H ∖ F. In each C_i, choose an arbitrary spanning tree on its vertices and
assign weight k to every tree edge. Let Ĥ consist of these weighted synthetic two-vertex edges and all
the unweighted original edges in F. Then, for every S ⊆ V, min{cut_H(S), k} = min{cut_Ĥ(S), k}."

Here the synthetic edges are any family `Tr` of two-vertex sets whose graph has exactly the connected
components of `H ∖ F` (a spanning tree of each component is one such family), with weight `k`, and the
edges of `F` have weight `1`.

**Formalization Note.** Connectivity of `H ∖ F` is reachability in its two-section. The hypergraph is
any finite simple hypergraph on `Fin n`; uniformity is not needed. -/
theorem lemma_7_1 {n : ℕ} (E F Tr : Finset (Finset (Fin n))) (k : ℕ) (hF1 : crisp E k ⊆ F)
    (hF2 : F ⊆ E) (hTr2 : ∀ t ∈ Tr, t.card = 2)
    (hTr : ∀ u v : Fin n, (twoSection Tr).Reachable u v ↔ (twoSection (E \ F)).Reachable u v)
    (S : Finset (Fin n)) :
    min (cut E S) k =
      min (cutW (Tr.toList.map (fun t => (t, k)) ++ F.toList.map (fun e => (e, 1))) S) k := by sorry

end HypRecov
