-- Prove2me | Theorems.Thm_GyoriLovasz_theorem_1_feac
-- name    : GyoriLovasz.theorem_1_feac
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:27.041762+00:00
-- url     : https://prove2.me/theorems/6b742c23-0681-4e43-9e8e-fb08cb82e4e2
-- title:
--   Proof of Theorem 1, p.23 — a k-T-connected graph satisfies the Flow-Essential Assignment Condition
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, $|T|=k$, that is $k$-$T$-connected, and let $c_t\in\mathbb N$ ($t\in T$) satisfy $\sum_{t\in T}c_t=|V\setminus T|$. Then
--
--   1. every terminal $t\in T$ is essential for every $v\in V\setminus T$; and
--   2. $G$ satisfies the Flow-Essential Assignment Condition for $c$.
--
--   This is the reduction of Theorem 1 to Theorem 2. The graph is arbitrary: no standing assumption of §2 is used.
--
--   Differences from the source:
--
--   - encoding: terminals T of G (T ⊆ V, §2, p.14) → hypothesis T ⊆ G.verts; reason: terminals are vertices of the graph
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), proof of Theorem 1, p.23

import Mathlib
import Definitions.Def_GyoriLovasz_IsWitness
import Definitions.Def_GyoriLovasz_IsKTConnected

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Proof of Theorem 1, the reduction.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), proof of Theorem 1, p.23: "We will show that if G is k-T-connected, then it satisfies the Flow-Essential Assignment Condition. To
see this, note that for every vertex v ∈ V \ T, κ_G(v) = k = |T|. Thus every terminal is essential for every vertex since removing any terminal decreases κ_G(v) by 1. Any assignment
of vertices to the terminals that respects the sizes shows the Flow-Essential Assignment Condition."

**Formalization Note.** On any directed graph with `T ⊆ V`, as in Theorem 1. The capacity hypothesis is that of Theorem 1. -/
theorem theorem_1_feac (G : DG V) (T : Finset V) (c : V → ℕ) (hT : T ⊆ G.verts)
    (hconn : IsKTConnected G T) (hsum : ∑ t ∈ T, c t = (G.verts \ T).card) :
    (∀ v ∈ G.verts \ T, ∀ t ∈ T, IsEssential G T v t) ∧ FEAC G T c := by sorry

end GyoriLovasz
