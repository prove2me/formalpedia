-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_4_14
-- name    : GyoriLovasz.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:54.106667+00:00
-- url     : https://prove2.me/theorems/2d7ce81a-10ba-4217-b9d1-80f935dccfb2
-- title:
--   Lemma 4.14 — transfer of criticality
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T=\{t_1,\dots,t_k\}\subseteq V$, no self-loops and no edge leaving a terminal. Let $M=\{(p_i,t_i):i\in[k]\}$ be a matching from pre-terminals to terminals, and for every $i$ let $e_i=(p_i,q_i)\in E$ be an edge distinct from $(p_i,t_i)$. Let $v\in V\setminus T$, $t\in T$ and $i\in[k]$, and assume that $e_i$ is critical for assigning $v$ to $t$. Then for every $j\in[k]$,
--   $$e_j\ \text{critical for assigning } v \text{ to } t_i\ \Longrightarrow\ e_j\ \text{critical for assigning } v \text{ to } t.$$
--
--   This is the step that makes the potential $\Phi$ decrease under a cycle shift (Lemma 4.12).
--
--   Differences from the source:
--
--   - encoding: indices i, j ∈ [k], terminal t_i, edge e_i → indices are the terminals themselves: t_i is i ∈ T and e_i is sec i; reason: a bijection between [k] and T; no instance changes
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 4.14, p.33

import Mathlib
import Definitions.Def_GyoriLovasz_IsCritical
import Definitions.Def_GyoriLovasz_IsTermMatching
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 4.14 (Transfer of criticality).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 4.14, p.33: "Let G = (V, E) be a directed graph with terminal set
T = {t_1, ..., t_k}. Let M = {(p_i, t_i) : i ∈ [k]} be a matching from pre-terminals to terminals, and for every i ∈ [k], let
e_i = (p_i, q_i) be an edge distinct from (p_i, t_i). Let v ∈ V \ T, let t ∈ T, and let i ∈ [k]. Assume that e_i is critical for assigning
v to t. Then every edge e_j that is critical for assigning v to t_i is also critical for assigning v to t."

**Formalization Note.** Indices `i, j ∈ [k]` are the terminals `i, j ∈ T` themselves: `t_i` is `i`, and `e_i` is `sec i`. `Std` and
`T ⊆ V` are the standing assumptions of §2. -/
theorem lemma_4_14 (G : DG V) (T : Finset V) (hstd : Std G T) (hT : T ⊆ G.verts) {p : V → V}
    {sec : V → V × V} (hp : IsTermMatching G T p) (hs : IsSecondary G T p sec) {v t i : V}
    (hv : v ∈ G.verts \ T) (ht : t ∈ T) (hi : i ∈ T) (hcrit : IsCritical G T (sec i) v t) :
    ∀ j ∈ T, IsCritical G T (sec j) v i → IsCritical G T (sec j) v t := by sorry

end GyoriLovasz
