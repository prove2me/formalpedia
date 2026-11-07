-- Prove2me | Theorems.Thm_GyoriLovasz_theorem_6_run
-- name    : GyoriLovasz.theorem_6_run
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:54.856949+00:00
-- url     : https://prove2.me/theorems/c52ec525-5d70-4c25-9633-5447dd04f89e
-- title:
--   Theorem 6 — GLPartition returns a valid partition (correctness and call bound; time bound: theorem_2)
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, no self-loops and no edge leaving a terminal, and let $\varphi$ be a flow-essential assignment for capacities $c$. Then
--
--   1. a run of GLPartition$(G,T,c,\varphi)$ exists, on some sequence of the algorithm's choices;
--   2. every run, on every sequence of choices, returns a valid partition $\langle V_t\rangle_{t\in T}$: for every $t\in T$, $t\in V_t$, $|V_t|=c_t+1$ and $G[V_t]$ is connected to $t$;
--   3. every run makes at most
--   $$|V|+|E|$$
--   recursive calls.
--
--   Clause 1 with clause 2 excludes a state at which the algorithm is stuck; clause 3 is the bound of the proof (p.28). Theorem 2 follows by computing a witness with one bipartite flow.
--
--   Differences from the source:
--
--   - reading: "GLPartition(G, T, c, φ) terminates in polynomial time and returns a partition" → a run exists, every run returns a valid partition, and every run makes at most |V| + |E| recursive calls (p.28); no running time; reason: the procedure is idealized, with no machine model; the machine cost is carried by theorem_2 (paper.md decision 9)
--   - encoding: the algorithm GLPartition with its free choices (which zero terminal, which pre-terminal, matching, secondary edges, labels, cycle, exit edge) → the inductive relation GLRun with every choice as an argument; reason: a statement over all runs covers every execution
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 6, p.25; proof of Theorem 6, p.28

import Mathlib
import Definitions.Def_GyoriLovasz_IsWitness
import Definitions.Def_GyoriLovasz_IsGLPartition
import Definitions.Def_GyoriLovasz_GLRun
import Definitions.Def_GyoriLovasz_Std

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Theorem 6, correctness and call bound (time bound: `theorem_2`).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 6, p.25: "Let (G, T, c, φ) satisfy the Flow-Essential Assignment Condition. Then
GLPartition(G, T, c, φ) terminates in polynomial time and returns a partition ⟨V_1, ..., V_k⟩ such that, for every i ∈ [k], t_i ∈ V_i, |V_i| = c_i + 1, and G[V_i] is connected to t_i."

A run exists on every witnessed instance, so no state is stuck; every run returns a valid partition and makes at most `|V| + |E|` recursive calls (p.28).

**Formalization Note.** `GLRun` records every free choice, so "every run" covers all choices of the algorithm. The machine cost is carried by `theorem_2`. `Std` and `T ⊆ V` are
the standing assumptions of §2. -/
theorem theorem_6_run (G : DG V) (T : Finset V) (c : V → ℕ) (φ : V → V) (hstd : Std G T)
    (hT : T ⊆ G.verts) (hw : IsWitness G T c φ) :
    (∃ n parts, GLRun G T c φ n parts) ∧
      ∀ n parts, GLRun G T c φ n parts →
        IsGLPartition G T c parts ∧ n ≤ G.verts.card + G.arcs.card := by sorry

end GyoriLovasz
