-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_4_8
-- name    : GyoriLovasz.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:41.223217+00:00
-- url     : https://prove2.me/theorems/1cd13bf3-756d-4acf-bc1d-5b73a9b9df79
-- title:
--   Lemma 4.8 — a matching from pre-terminals to terminals exists
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T=\{t_1,\dots,t_k\}\subseteq V$, no self-loops and no edge leaving a terminal, and let $\varphi$ be a flow-essential assignment for capacities $c$ with $c_i>0$ for all $i\in[k]$. Then there exist distinct vertices $p_1,\dots,p_k\in\mathrm{PT}(G,T)$ such that
--   $$(p_i,t_i)\in E\quad\text{for all } i\in[k].$$
--
--   This is line 1 of Algorithm 3.
--
--   Differences from the source:
--
--   - encoding: distinct p_1, …, p_k ∈ PT(G, T) with (p_i, t_i) ∈ E → a map p on T, injective on T, with p t ∈ V ∖ T and (p t, t) ∈ E; reason: indexing by the terminal itself; p t ∈ PT(G, T) follows from the edge
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 4.8, p.29

import Mathlib
import Definitions.Def_GyoriLovasz_IsWitness
import Definitions.Def_GyoriLovasz_IsTermMatching
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 4.8.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 4.8, p.29: "Let (G, T, c, φ) satisfy the Flow-Essential Assignment Condition. Assume that c_i > 0 for all
i ∈ [k]. Then there exists a matching from pre-terminals to terminals, that is, there exist distinct vertices p_1, ..., p_k ∈ PT(G, T)
such that (p_i, t_i) ∈ E for all i ∈ [k]."

**Formalization Note.** `Std` and `T ⊆ V` are the standing assumptions of §2. -/
theorem lemma_4_8 (G : DG V) (T : Finset V) (c : V → ℕ) (φ : V → V) (hstd : Std G T)
    (hT : T ⊆ G.verts) (hw : IsWitness G T c φ) (hc : ∀ t ∈ T, 0 < c t) :
    ∃ p, IsTermMatching G T p := by sorry

end GyoriLovasz
