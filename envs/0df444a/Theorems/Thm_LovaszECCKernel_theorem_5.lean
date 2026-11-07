-- Prove2me | Theorems.Thm_LovaszECCKernel_theorem_5
-- name    : LovaszECCKernel.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:50.637836+00:00
-- url     : https://prove2.me/theorems/2649788d-eb8a-4b9d-bc37-94d09c1a432e
-- title:
--   Theorem 5 (Stability for Lovász's theorem) — $\mathrm{ecc}(G)\ge\mathrm{Lb}(G)-k$ implies $22k$ edits to complete multipartite
-- statement:
--   **Theorem 5.** For every integer $k\ge0$ and every finite simple graph $G$, if
--   $$\mathrm{ecc}(G)\ \ge\ \mathrm{Lb}(G)-k,$$
--   then there is a set $M\subseteq\binom{V(G)}{2}$ with $|M|\le22k$ such that $G\triangle M$ is complete multipartite.
--
--   This is the paper's fine-grained stability theorem: graphs that cannot beat Lovász's bound by $k$ are $O(k)$ edits from the extremal structure, with a constant independent of $|V(G)|$. For $k=0$ it says that $\mathrm{ecc}(G)=\mathrm{Lb}(G)$ forces $G$ to be complete multipartite.
--
--   Differences from the source:
--   - encoding: complete multipartite (complete r-partite for some r ≥ 2, empty parts allowed) → Mathlib's SimpleGraph.IsCompleteMultipartite (non-adjacency is transitive); reason: the same graphs; empty parts let the edgeless graph count as complete 2-partite
--   - encoding: the hypothesis ecc(G) ≥ Lb(G) − k → compared in ℤ; reason: Lb(G) − k may be negative
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 5, p.6 (= PDF p.6); restated p.21

import Mathlib
import Definitions.Def_LovaszECCKernel_Lb
import Definitions.Def_LovaszECCKernel_ecc
import Definitions.Def_LovaszECCKernel_flip

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Theorem 5 (Stability for Lovász's Theorem)** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Theorem 5, p.6 (= PDF p.6); restated
word for word on p.21): "For any integer k ≥ 0 and any graph G, if ecc(G) ≥ Lb(G) − k, then there
exists a set M ⊆ (V(G) choose 2) of size at most 22k such that G△M is complete multipartite."

**Formalization Note** The hypothesis is compared in `ℤ`. "Complete multipartite" is Mathlib's
`SimpleGraph.IsCompleteMultipartite` (non-adjacency is transitive), which allows any number of
parts, including one (the edgeless graph). -/
theorem theorem_5 {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (h : (Lb G : ℤ) - k ≤ ecc G) :
    ∃ M : Finset (Sym2 V), IsPairSet M ∧ M.card ≤ 22 * k ∧
      (flip G M).IsCompleteMultipartite := by sorry

end LovaszECCKernel
