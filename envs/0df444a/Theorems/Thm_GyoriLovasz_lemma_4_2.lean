-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_4_2
-- name    : GyoriLovasz.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:14.798991+00:00
-- url     : https://prove2.me/theorems/35ab3093-6450-4dc9-8ff5-ecbcf531679e
-- title:
--   Lemma 4.2 — removing a terminal with zero capacity
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, no self-loops and no edge leaving a terminal, and let $\varphi$ be a flow-essential assignment for capacities $c$. Let $t_i\in T$ have $c_i=0$, and let $G'=G\setminus\{t_i\}$. Then
--
--   1. $\varphi$ is a flow-essential assignment of $(G',T\setminus\{t_i\})$ for the capacities $c'=(c_j)_{j\neq i}$;
--   2. if $\langle V_j\rangle_{j\neq i}$ is a valid partition for $(G',T\setminus\{t_i\},c')$, then the parts with $V_i=\{t_i\}$ added form a valid partition for $(G,T,c)$.
--
--   This justifies lines 3–8 of Algorithm 2.
--
--   Differences from the source:
--
--   - encoding: c′ = (c_1, …, c_{i−1}, c_{i+1}, …, c_k) and the parts V_j for j ≠ i → the same capacity map c read on T ∖ {t_i}; parts as a map on terminals, with the part of t_i overwritten by {t_i}; reason: only the values on the remaining terminals are read
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 4.2, p.26

import Mathlib
import Definitions.Def_GyoriLovasz_IsWitness
import Definitions.Def_GyoriLovasz_IsGLPartition
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 4.2 (Removing a terminal with zero capacity).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 4.2, p.26: "Let (G, T, c, φ) satisfy the Flow-Essential Assignment Condition.
Assume that there exists a terminal t_i such that c_i = 0. Let G′ be the graph obtained by removing t_i from G. Let c′ = (c_1, ..., c_{i−1}, c_{i+1}, ..., c_k)
be the vector of capacities for the remaining terminals. Then (G′, T \ {t_i}, c′, φ) also satisfies the Flow-Essential Assignment Condition. Let
⟨V_1, ..., V_{i−1}, V_{i+1}, ...V_k⟩ be a partition for (G′, T \ {t_i}, c′, φ). Then ⟨V_1, ..., V_{i−1}, V_i = {t_i}, V_{i+1}, ...V_k⟩ is a valid partition
for the original instance."

**Formalization Note.** `c′` is `c` read on `T \ {t}`. `Std` and `T ⊆ V` are the standing assumptions of §2. -/
theorem lemma_4_2 (G : DG V) (T : Finset V) (c : V → ℕ) (φ : V → V) (hstd : Std G T)
    (hT : T ⊆ G.verts) (hw : IsWitness G T c φ) {t : V} (ht : t ∈ T) (hc : c t = 0) :
    IsWitness (G.deleteVertex t) (T.erase t) c φ ∧
      ∀ parts, IsGLPartition (G.deleteVertex t) (T.erase t) c parts →
        IsGLPartition G T c (Function.update parts t {t}) := by sorry

end GyoriLovasz
