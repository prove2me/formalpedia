-- Prove2me | Theorems.Thm_LovaszECCKernel_proposition_5
-- name    : LovaszECCKernel.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:06.976175+00:00
-- url     : https://prove2.me/theorems/970790c7-3b65-4ae9-bf31-5e8ecad9154c
-- title:
--   Proposition 5 (Lovász) — Type-A cliques $\le s(|\overline E(G)|)$, Type-B cliques $\le|\overline E(G)|$
-- statement:
--   **Proposition 5.** Let $G$ be a finite simple graph and $\mathcal C$ the Lovász Clique Cover of an m.c.d.s. $C_1,\dots,C_t$ of $G$. Then
--   1. the number of Type-A cliques of $\mathcal C$ is at most $s(|\overline E(G)|)$;
--   2. the number of Type-B cliques of $\mathcal C$ is at most $|\overline E(G)|$.
--
--   Together the two bounds give Lovász's bound $|\mathcal C|\le\mathrm{Lb}(G)$; the refined form is what Lemma 1 uses to save $k$ cliques.
--
--   Differences from the source:
--   - reading: an m.c.d.s. has t₂ ∈ [t] (Definition 1) → t₂ ∈ {0, …, t}; reason: edgeless graphs have only singleton cliques (t₂ = 0); the paper uses such sequences (Lovász's construction, step 7 of Lemma 8's proof), and the printed [t] would leave them without an m.c.d.s.; the Lean statement covers the printed sequences too
--   - encoding: cliques C₁, …, C_t, 1-based → a list indexed from 0; reason: Lean convention; the same sequences
--   - generalization: the number of Type-B cliques in C (a set) → the number of index pairs (i, v) defining Type-B cliques, counted with multiplicity; reason: the count with multiplicity is at least the number of distinct Type-B cliques, so the Lean bound implies the printed one
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Proposition 5, p.20 (= PDF p.20)

import Mathlib
import Definitions.Def_LovaszECCKernel_nonEdges
import Definitions.Def_LovaszECCKernel_sMax
import Definitions.Def_LovaszECCKernel_IsMCDS
import Definitions.Def_LovaszECCKernel_LCC

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Proposition 5 (Lovász [Lov68])** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Proposition 5, p.20 (= PDF p.20)): "Let C be an LCC of
G. The number of Type-A cliques in C is at most s(|E̅(G)|), and the number of Type-B cliques in C is
at most |E̅(G)|."

**Formalization Note** `C` is the LCC of an arbitrary m.c.d.s. `L` of `G` (Definitions 1–2, p.19).
The Type-A cliques are counted by `typeA L` (`= t₂`), the Type-B cliques by `typeBCount G L`, i.e.
with multiplicity over their indices `(i, v)`, which is at least their number as a set. -/
theorem proposition_5 {V : Type*} [Fintype V] (G : SimpleGraph V) (L : List (Finset V))
    (hL : IsMCDS G L) :
    typeA L ≤ sMax (nonEdges G).card ∧ typeBCount G L ≤ (nonEdges G).card := by sorry

end LovaszECCKernel
