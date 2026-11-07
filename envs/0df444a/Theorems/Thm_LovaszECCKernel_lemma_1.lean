-- Prove2me | Theorems.Thm_LovaszECCKernel_lemma_1
-- name    : LovaszECCKernel.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:44.104093+00:00
-- url     : https://prove2.me/theorems/ddc51032-f23b-44b9-85e6-ebef3a1899a4
-- title:
--   Lemma 1 — enough extra non-edges and singletons in an m.c.d.s. give $\mathrm{ecc}(G)\le\mathrm{Lb}(G)-k$
-- statement:
--   **Lemma 1.** Let $k\ge0$ be an integer and $G$ a finite simple graph. If some m.c.d.s. $C_1,\dots,C_t$ of $G$, with $t_2$ cliques of size at least two, satisfies
--   $$\sum_{1\le i<j\le t}\bigl(|\overline E(C_i,C_j)|-|C_j|\bigr)+\binom{t-t_2}{2}\ \ge\ k,$$
--   then $\mathrm{ecc}(G)\le\mathrm{Lb}(G)-k$.
--
--   Here $\overline E(C_i,C_j)$ is the set of non-edges between $C_i$ and $C_j$. The lemma is the certificate the kernel looks for: an m.c.d.s. whose non-edges are "wasted" or whose singletons are many proves a yes-instance.
--
--   Differences from the source:
--   - reading: an m.c.d.s. has t₂ ∈ [t] (Definition 1) → t₂ ∈ {0, …, t}; reason: edgeless graphs have only singleton cliques (t₂ = 0); the paper uses such sequences (Lovász's construction, step 7 of Lemma 8's proof), and the printed [t] would leave them without an m.c.d.s.; the Lean statement covers the printed sequences too
--   - encoding: cliques C₁, …, C_t, 1-based → a list indexed from 0; reason: Lean convention; the same sequences
--   - encoding: the sum and the comparison with k over the integers → computed in ℤ; reason: no truncated subtraction; the same inequality
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 1, p.20 (= PDF p.20)

import Mathlib
import Definitions.Def_LovaszECCKernel_InLb
import Definitions.Def_LovaszECCKernel_IsMCDS
import Definitions.Def_LovaszECCKernel_crossEdges

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Lemma 1** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Lemma 1, p.20 (= PDF p.20)): "Let k ≥ 0 be an integer. If there exists an
m.c.d.s. C1, C2, . . . , Ct in G such that
Σ_{1≤i<j≤t} (|E̅(Ci, Cj)| − |Cj|) + (t − t2 choose 2) ≥ k,
then ecc(G) ≤ Lb(G) − k."

**Formalization Note** The m.c.d.s. is a list indexed from `0` (`L.getD i ∅` is the paper's
`C_{i+1}`); `t = L.length` and `t₂ = typeA L`. The sum is computed in `ℤ`;
`|E̅(Ci, Cj)|` is `crossNonEdges`, the number of non-edges between the two (disjoint) cliques. -/
theorem lemma_1 {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (L : List (Finset V))
    (hL : IsMCDS G L)
    (h : (k : ℤ) ≤ (∑ j ∈ Finset.range L.length, ∑ i ∈ Finset.range j,
        ((crossNonEdges G (L.getD i ∅) (L.getD j ∅) : ℤ) - ((L.getD j ∅).card : ℤ))) +
        ((L.length - typeA L).choose 2 : ℕ)) :
    InLb G k := by sorry

end LovaszECCKernel
