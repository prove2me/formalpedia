-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_4_12
-- name    : GyoriLovasz.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:29.906317+00:00
-- url     : https://prove2.me/theorems/a3c10c3d-caa0-4fda-afe3-a28dc80624a2
-- title:
--   Lemma 4.12 — a cycle shift keeps the condition and lowers the potential (corrected: k ≥ 1)
-- statement:
--   Let $G=(V,E)$ be a directed graph with a nonempty terminal set $T\subseteq V$, no self-loops and no edge leaving a terminal, and let $\varphi$ be a flow-essential assignment for capacities $c$. Let $M=\{(p_1,t_1),\dots,(p_k,t_k)\}$ be a matching from pre-terminals to terminals, and for every $i$ let $e_i=(p_i,q_i)\in E$ be an edge distinct from $(p_i,t_i)$ that is critical for assigning a vertex $v_i\in V\setminus T$ to $\varphi(v_i)$. Let $\mathcal R$ be the reassignment graph on $T$ with the edges $\varphi(v_i)\to t_i$ labeled $v_i$. Then
--
--   1. $\mathcal R$ contains a directed cycle;
--   2. for **every** directed cycle $\mathcal C$ of $\mathcal R$, the shift of $\varphi$ along $\mathcal C$ exists, and every assignment $\varphi'$ obtained by the shift is again a flow-essential assignment for $c$, with
--   $$\Phi(\varphi')<\Phi(\varphi).$$
--
--   The potential $\Phi$ is computed with the secondary edges $e_1,\dots,e_k$. This lemma bounds the number of iterations of Algorithm 3.
--
--   Differences from the source:
--
--   - correction: no condition on k; "Then R contains a directed cycle" → hypothesis T.Nonempty (k ≥ 1); reason: at k = 0 with the empty graph every hypothesis holds (the empty assignment is flow-essential, the matching and edges are empty) but R has no vertex and no cycle
--   - encoding: "Let C be such a cycle" / "Let φ′ be the assignment obtained by shifting φ along C" → the conclusion for every directed cycle of R, including the existence of the shifted assignment (the labels on a cycle are distinct); reason: Algorithm 3, line 11 may pick any cycle; the shift is a relation, so its existence is stated
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 4.12, p.31

import Mathlib
import Definitions.Def_GyoriLovasz_IsWitness
import Definitions.Def_GyoriLovasz_IsTermMatching
import Definitions.Def_GyoriLovasz_Phi
import Definitions.Def_GyoriLovasz_IsShift
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 4.12 (Cycle shift decreases the potential).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 4.12, p.31: "Let (G, T, c, φ) satisfy the Flow-Essential
Assignment Condition. Let M = {(p_1, t_1), ..., (p_k, t_k)} be a matching from pre-terminals to terminals. For every i ∈ [k], let
e_i = (p_i, q_i) be an edge distinct from (p_i, t_i), and assume that e_i is critical for assigning a vertex v_i to φ(v_i). Let R be the
reassignment graph on T containing, for every i ∈ [k], the edge φ(v_i) → t_i labeled by v_i. Then R contains a directed cycle C. Let φ′
be the assignment obtained by shifting φ along C. Then (G, T, c, φ′) satisfies the Flow-Essential Assignment Condition and
Φ(φ′) < Φ(φ)."

**Formalization Note.** The conclusion is for every directed cycle of `R`, as the algorithm may pick any (Algorithm 3, line 11), and
it says that the shift exists, that is, that the labels on a cycle are distinct. `T.Nonempty` is added: at `k = 0` the graph `R` is
empty and has no cycle. `Std` and `T ⊆ V` are the standing assumptions of §2. -/
theorem lemma_4_12 (G : DG V) (T : Finset V) (c : V → ℕ) (φ : V → V) (hstd : Std G T)
    (hT : T ⊆ G.verts) (hk : T.Nonempty) (hw : IsWitness G T c φ) {p : V → V} {sec : V → V × V}
    (hp : IsTermMatching G T p) (hs : IsSecondary G T p sec) {v : V → V}
    (hv : ∀ t ∈ T, v t ∈ G.verts \ T ∧ IsCritical G T (sec t) (v t) (φ (v t))) :
    (∃ C, IsShiftCycle T φ v C) ∧
      ∀ C, IsShiftCycle T φ v C →
        (∃ φ', IsShift φ v C φ') ∧
          ∀ φ', IsShift φ v C φ' → IsWitness G T c φ' ∧ Phi G T sec φ' < Phi G T sec φ := by sorry

end GyoriLovasz
