-- Prove2me | Theorems.Thm_GyoriLovasz_Supplement_theorem_3
-- name    : GyoriLovasz.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:13:57.035694+00:00
-- url     : https://prove2.me/theorems/379a8008-3d1f-40dd-85f7-b61e52ccb078
-- title:
--   Theorem 3 — weighted Győri–Lovász in polynomial time: parts connected to their terminals, weight at most $c_t + w_{\max} - 1$
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T$, $|T|=k$. Each non-terminal $v\in V\setminus T$ has a positive integer weight $w_v$, each terminal $t\in T$ has a nonnegative integer capacity $c_t$, and
--
--   $$
--   \sum_{v\in V\setminus T}w_v\le\sum_{t\in T}c_t .
--   $$
--
--   Let $w_{\max}=\max_{v\in V\setminus T}w_v$. If $G$ is $k$-$T$-connected (every non-terminal has $k$ paths to distinct terminals, vertex-disjoint apart from their start), then there is a **polynomial-time algorithm** that partitions $V$ into parts $\langle V_t\rangle_{t\in T}$ with $t\in V_t$, $G[V_t]$ connected to $t$, and
--
--   $$
--   \sum_{v\in V_t\setminus T}w_v\le c_t+w_{\max}-1\qquad\text{for every } t\in T .
--   $$
--
--   Weights and capacities are given in binary, so the running time is polynomial in their bit length. This is the weighted analogue of Theorem 1 and gives an algorithm for the existence theorem behind the confluent-flow result of Chen et al.; the additive $w_{\max}-1$ cannot be avoided.
--
--   **Formalization Note** One Turing machine (`Turing.TM2ComputableInPolyTime` with the injective encoders `encWInstance` and `encLabels`) works for all instances; its output, a label per vertex, must be a valid weighted partition on every well-formed instance satisfying the hypotheses. The graph is arbitrary, as in the printed statement.
--
--   Differences from the source:
--   - encoding: there is a polynomial-time algorithm → ∃ alg, Nonempty (Turing.TM2ComputableInPolyTime encWInstance encLabels alg), before ∀ I; reason: the paper names no machine; polynomial time on discrete input is model-robust; one machine for all instances; numbers in binary as on p.13
--   - encoding: a directed graph G with terminal set T, capacities c_t, weights w_v → WInstance on vertices 0..n−1 with WellFormed (terminals are distinct vertices, one weight per vertex); reason: same instances, written as data
--   - encoding: each non-terminal vertex v has a positive integer weight w_v → hypothesis PosWeights; reason: same instances
--   - encoding: partitions V(G) into parts ⟨V_t⟩_{t∈T} → a label list with one label < k per vertex; part i belongs to t_i; reason: a labelling is a partition indexed by the terminals
--   - encoding: ∑_{v∈V_t∖T} w_v ≤ c_t + w_max − 1 → ≤ c_i + wmax − 1 in ℕ; reason: exact when a non-terminal exists (w_max ≥ 1); otherwise every part has weight 0
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 3, p.11 (restated p.37)

import Mathlib
import Definitions.Def_GyoriLovasz_IsKTConnected
import Definitions.Def_GyoriLovasz_encInstance
import Definitions.Def_GyoriLovasz_Supplement_WInstance
import Definitions.Def_GyoriLovasz_Supplement_encWInstance
import Definitions.Def_GyoriLovasz_Supplement_IsWLabelPartition

namespace GyoriLovasz

namespace Supplement

/-- **Theorem 3.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 3, p.11 (restated p.37): "Let G be a directed graph with
terminal set T. Each non-terminal vertex v has a positive integer weight w_v, and each terminal t has a nonnegative
integer capacity c_t, with ∑_{v∈V\T} w_v ≤ ∑_{t∈T} c_t. If G is k-T-connected, then there is a polynomial-time
algorithm that partitions V(G) into parts ⟨V_t⟩_{t∈T} such that t ∈ V_t, G[V_t] is connected to t, and
∑_{v∈V_t\T} w_v ≤ c_t + w_max − 1 for every terminal t ∈ T."

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with the injective encoders `encWInstance`
(all numbers, weights included, in binary) and `encLabels`, exactly as in the published `theorem_1`: one machine for
all `k` (`∃ alg` comes before the instance), which halts in polynomial time on every encoded input, and whose output is
correct on the instances of the theorem. The paper names no machine; polynomial time on discrete input does not depend
on the reasonable model. `w_max` is the maximum weight of a non-terminal of the input (p.14). The graph is arbitrary,
as in the printed statement. -/
theorem theorem_3 :
    ∃ alg : WInstance → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encWInstance encLabels alg) ∧
        ∀ I : WInstance, I.WellFormed → I.PosWeights → IsKTConnected I.base.toDG I.base.termSet →
          ∑ v ∈ I.nonTerms, I.w v ≤ (I.base.terms.map Prod.snd).sum →
            IsWLabelPartition I (alg I) := by sorry

end Supplement

end GyoriLovasz
