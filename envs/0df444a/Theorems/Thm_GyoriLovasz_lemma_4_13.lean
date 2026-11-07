-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_4_13
-- name    : GyoriLovasz.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:40.017431+00:00
-- url     : https://prove2.me/theorems/224b2ba3-abc7-48fa-8afb-26977ea58c67
-- title:
--   Lemma 4.13 — a secondary edge is never critical for its own terminal
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, no self-loops and no edge leaving a terminal. Let $p_i\in\mathrm{PT}(G,T)$ with $(p_i,t_i)\in E$, and let $e_i=(p_i,q_i)\in E$ be distinct from $(p_i,t_i)$. Then for every $v\in V\setminus T$,
--   $$e_i \text{ is not critical for assigning } v \text{ to } t_i.$$
--
--   Together with Lemma 4.14 it shows that a shift lowers the potential $\Phi$.
--
--   Differences from the source:
--
--   - encoding: p_i ∈ PT(G, T), e_i = (p_i, q_i) an edge distinct from (p_i, t_i) → p ∈ V ∖ T with (p, t_i) ∈ E, (p, q) ∈ E and q ≠ t_i; reason: the same conditions; p ∈ PT(G, T) follows from the edge (p, t_i)
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 4.13, p.32

import Mathlib
import Definitions.Def_GyoriLovasz_IsCritical
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 4.13.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 4.13, p.32: "Let G = (V, E) be a directed graph with terminal set T. Let p_i ∈ PT(G, T) be a pre-terminal
and t_i ∈ T be a terminal corresponding to p_i, i.e., (p_i, t_i) ∈ E. Let e_i = (p_i, q_i) be an edge distinct from (p_i, t_i). Then e_i is
not critical for assigning any vertex v ∈ V \ T to t_i."

**Formalization Note.** `Std` and `T ⊆ V` are the standing assumptions of §2. -/
theorem lemma_4_13 (G : DG V) (T : Finset V) (hstd : Std G T) (hT : T ⊆ G.verts) {p ti q v : V}
    (hp : p ∈ G.verts \ T) (hti : ti ∈ T) (hpt : (p, ti) ∈ G.arcs) (hpq : (p, q) ∈ G.arcs) (hne : q ≠ ti)
    (hv : v ∈ G.verts \ T) : ¬ IsCritical G T (p, q) v ti := by sorry

end GyoriLovasz
