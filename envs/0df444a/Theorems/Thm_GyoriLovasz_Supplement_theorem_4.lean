-- Prove2me | Theorems.Thm_GyoriLovasz_Supplement_theorem_4
-- name    : GyoriLovasz.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:14:42.345199+00:00
-- url     : https://prove2.me/theorems/d842c188-688f-462b-a7eb-15d15be7fac0
-- title:
--   Theorem 4 — weighted partition in polynomial time under the Flow-Essential Split-Assignment Condition
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T$. Each non-terminal $v\in V\setminus T$ has a positive integer weight $w_v$ and each terminal $t$ has a nonnegative integer capacity $c_t$; let $w_{\max}=\max_{v\in V\setminus T}w_v$. If $G$ satisfies the **Flow-Essential Split-Assignment Condition** (there is $\psi:(V\setminus T)\times T\to\mathbb N$ with $\sum_t\psi(v,t)=w_v$, $\psi(v,t)>0$ only for terminals $t$ essential for $v$, and $\sum_v\psi(v,t)\le c_t$), then there is a **polynomial-time algorithm** that partitions $V$ into parts $\langle V_t\rangle_{t\in T}$ with $t\in V_t$, $G[V_t]$ connected to $t$, and
--
--   $$
--   \sum_{v\in V_t\setminus T}w_v\le c_t+w_{\max}-1\qquad\text{for every } t\in T .
--   $$
--
--   Theorem 4 strengthens Theorem 3: in a $k$-$T$-connected graph every terminal is essential for every vertex, so the condition holds whenever the capacities cover the total weight. The algorithm is not given the witness $\psi$.
--
--   **Formalization Note** As in Theorem 3, one Turing machine with binary input encoding `encWInstance` and output encoding `encLabels`; the condition is `FESAC` on the input's graph, terminal set, capacities and weights. The graph is arbitrary, as in the printed statement.
--
--   Differences from the source:
--   - encoding: there is a polynomial-time algorithm → ∃ alg, Nonempty (Turing.TM2ComputableInPolyTime encWInstance encLabels alg), before ∀ I; reason: the paper names no machine; polynomial time on discrete input is model-robust; one machine for all instances; numbers in binary as on p.13
--   - encoding: a directed graph G with terminal set T, capacities c_t, weights w_v → WInstance on vertices 0..n−1 with WellFormed (terminals are distinct vertices, one weight per vertex); reason: same instances, written as data
--   - encoding: each non-terminal vertex v has a positive integer weight w_v → hypothesis PosWeights; reason: same instances
--   - encoding: partitions V(G) into parts ⟨V_t⟩_{t∈T} → a label list with one label < k per vertex; part i belongs to t_i; reason: a labelling is a partition indexed by the terminals
--   - encoding: ∑_{v∈V_t∖T} w_v ≤ c_t + w_max − 1 → ≤ c_i + wmax − 1 in ℕ; reason: exact when a non-terminal exists (w_max ≥ 1); otherwise every part has weight 0
--   - encoding: ψ : (V∖T)×T → ℕ≥0 → ψ : V → V → ℕ, read only on (V∖T)×T; reason: values off the domain are never read; same condition
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 4, p.12 (restated p.37); Definition 1.3, p.12; Definition 3.5, p.21

import Mathlib
import Definitions.Def_GyoriLovasz_encInstance
import Definitions.Def_GyoriLovasz_Supplement_WInstance
import Definitions.Def_GyoriLovasz_Supplement_encWInstance
import Definitions.Def_GyoriLovasz_Supplement_IsWLabelPartition
import Definitions.Def_GyoriLovasz_Supplement_FESAC

namespace GyoriLovasz

namespace Supplement

/-- **Theorem 4.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 4, p.12 (restated p.37): "Let G be a directed graph with
terminal set T. Each non-terminal vertex v has a positive integer weight w_v, and each terminal t has a nonnegative
integer capacity c_t. If G satisfies the Flow-Essential Split-Assignment Condition, then there is a polynomial-time
algorithm that partitions V(G) into parts ⟨V_t⟩_{t∈T} such that t ∈ V_t, G[V_t] is connected to t, and
∑_{v∈V_t\T} w_v ≤ c_t + w_max − 1 for every terminal t ∈ T."

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with the injective encoders `encWInstance`
(all numbers in binary) and `encLabels`, as in the published `theorem_2`: one machine for all instances, halting in
polynomial time on every encoded input, correct on the instances of the theorem. The algorithm receives no witness. The
condition is `FESAC` on the graph of the input, its terminal set, the capacities `cap` and the weights `w`. The graph is
arbitrary, as in the printed statement. -/
theorem theorem_4 :
    ∃ alg : WInstance → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encWInstance encLabels alg) ∧
        ∀ I : WInstance, I.WellFormed → I.PosWeights →
          FESAC I.base.toDG I.base.termSet I.base.cap I.w →
            IsWLabelPartition I (alg I) := by sorry

end Supplement

end GyoriLovasz
