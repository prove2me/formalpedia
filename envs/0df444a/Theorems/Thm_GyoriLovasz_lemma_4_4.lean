-- Prove2me | Theorems.Thm_GyoriLovasz_lemma_4_4
-- name    : GyoriLovasz.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:15.276074+00:00
-- url     : https://prove2.me/theorems/fc4d9428-1a86-46b8-bdb8-3a9e3592b1e8
-- title:
--   Lemma 4.4 — contracting a pre-terminal of out-degree one
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, no self-loops and no edge leaving a terminal, and let $\varphi$ be a flow-essential assignment for capacities $c$. Let $p\in\mathrm{PT}(G,T)$ have $d^+(p)=1$, with its edge $(p,t_i)$, and let $G'$ be obtained by contracting $(p,t_i)$ into $t_i$. Let $c'$ be $c$ with $c_i$ decreased by one. Then
--
--   1. $\varphi'=\varphi\setminus\{p\}$ is a flow-essential assignment of $(G',T)$ for $c'$;
--   2. if $\langle V'_1,\dots,V'_k\rangle$ is a valid partition for $(G',T,c')$, then the partition obtained by replacing $V'_i$ with $V'_i\cup\{p\}$ is valid for $(G,T,c)$.
--
--   This justifies lines 9–15 of Algorithm 2.
--
--   Differences from the source:
--
--   - encoding: φ′ = φ ∖ {p}, c′ = c with c_i decreased by one → the same function φ, read on the smaller vertex set; Function.update c t (c t − 1); reason: φ is only read on V ∖ T; the subtraction does not truncate since the assignment puts p on t_i, so c_i ≥ 1
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 4.4, p.27

import Mathlib
import Definitions.Def_GyoriLovasz_IsWitness
import Definitions.Def_GyoriLovasz_IsGLPartition
import Definitions.Def_GyoriLovasz_PT
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Lemma 4.4 (Contracting a pre-terminal of out-degree one).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 4.4, p.27: "Let (G, T, c, φ) satisfy the Flow-Essential Assignment Condition. Assume that
there exists a pre-terminal p ∈ PT(G, T) such that d⁺(p) = 1, and let t_i be its corresponding terminal. Let G′ be the graph obtained by contracting the edge (p, t_i) into t_i.
Let φ′ = φ \ {p} be the assignment obtained by removing p from the domain of φ. Then (G′, T, c′, φ′) also satisfies the Flow-Essential Assignment Condition, where c′ is
obtained from c by decreasing c_i by one. Let ⟨V′_1, ..., V′_k⟩ be a partition for (G′, T, c′, φ′). Then ⟨V′_1, ..., V′_{i−1}, V′_i ∪ {p}, V′_{i+1}, ...V′_k⟩ is a valid
partition for the original instance."

**Formalization Note.** `φ \ {p}` is the same function `φ`, read on the smaller `V \ T`. The subtraction `c t - 1` does not truncate: the witness assigns `p` to `t`, so
`c t ≥ 1`. `Std` and `T ⊆ V` are the standing assumptions of §2. -/
theorem lemma_4_4 (G : DG V) (T : Finset V) (c : V → ℕ) (φ : V → V) (hstd : Std G T)
    (hT : T ⊆ G.verts) (hw : IsWitness G T c φ) {p t : V} (hp : p ∈ PT G T T) (ht : t ∈ T)
    (ha : (p, t) ∈ G.arcs) (hd : G.outDeg p = 1) :
    IsWitness (G.contract p t) T (Function.update c t (c t - 1)) φ ∧
      ∀ parts, IsGLPartition (G.contract p t) T (Function.update c t (c t - 1)) parts →
        IsGLPartition G T c (Function.update parts t (insert p (parts t))) := by sorry

end GyoriLovasz
