-- Prove2me | Theorems.Thm_GyoriLovasz_theorem_2
-- name    : GyoriLovasz.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:10.068834+00:00
-- url     : https://prove2.me/theorems/f82bae44-3ad1-4f26-a06c-84ba6ff501d6
-- title:
--   Theorem 2 — polynomial-time partition under the Flow-Essential Assignment Condition
-- statement:
--   There is a single polynomial-time algorithm with the following property. Let $G=(V,E)$ be a directed graph and $T=\{t_1,\dots,t_k\}$ a set of distinct terminals, and let $c_1,\dots,c_k$ be nonnegative integers with
--   $$\sum_{i=1}^k c_i=|V\setminus T|.$$
--   If $G$ satisfies the Flow-Essential Assignment Condition for these capacities, then on input $(G,T,c)$ the algorithm outputs a partition of $V$ into $V_1,\dots,V_k$ such that
--   $$t_i\in V_i,\qquad |V_i|=c_i+1,\qquad G[V_i]\text{ is connected to } t_i\quad(i\in[k]).$$
--
--   Theorem 2 strengthens Theorem 1, since $k$-$T$-connectivity implies the condition (proof of Theorem 1, p.23). The graph is arbitrary: it may have loops and edges leaving terminals.
--
--   **Formalization Note** The algorithm is a Mathlib multi-tape Turing machine (`Turing.TM2ComputableInPolyTime`) reading the input as the vertex count $n$ in binary, the edge list and the list of pairs $(t_i,c_i)$, and writing one label per vertex.
--
--   Differences from the source:
--
--   - reading: "there exists a polynomial-time algorithm" (no machine model is named) → ∃ alg with Turing.TM2ComputableInPolyTime encInstance encLabels alg: one Mathlib multi-tape Turing machine for all k, with binary numbers and a terminated-word encoding; reason: polynomial time on discrete inputs is the same class in every reasonable model; ∃ alg comes before the instance, so the algorithm is uniform
--   - encoding: an algorithm that works on the instances of the theorem → a total function, computed in polynomial time on every encoded input, and correct on the instances satisfying the hypotheses; reason: Mathlib's notion is total; the hypothesis can be tested in polynomial time by maximum flow and [] returned when it fails, so no instance is gained or lost
--   - encoding: G = (V, E), distinct terminals t_1, …, t_k, capacities c_i, ∑ c_i = |V ∖ T| → an Instance (n, edge list, list of (t_i, c_i)) with WellFormed (endpoints and terminals below n, terminals distinct), and ∑ c_i + k = n; reason: for k distinct terminals among n vertices |V ∖ T| = n − k; repeated edges denote one edge
--   - encoding: the partition V_1, …, V_k → a list of n labels below k, with V_i the vertices labelled i; reason: a labelling is a partition into k indexed parts
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 2, p.8 (restated p.23)

import Mathlib
import Definitions.Def_GyoriLovasz_IsWitness
import Definitions.Def_GyoriLovasz_encInstance
import Definitions.Def_GyoriLovasz_IsLabelPartition

namespace GyoriLovasz

/-- **Theorem 2.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 2, p.8 (restated p.23): "Let G = (V, E) be a directed graph and T = {t_1, ..., t_k} be a set of distinct terminals. Let c_1, ..., c_k be nonnegative integers such that
∑_{i=1}^k c_i = |V \ T|. If G satisfies the Flow-Essential Assignment Condition for these capacities, then there exists a polynomial-time algorithm that partitions the vertices of the graph into V_1, ..., V_k,
such that t_i ∈ V_i, |V_i| = c_i + 1, and the induced subgraph G[V_i] is connected to t_i."

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with the injective encoders `encInstance` (binary numbers) and `encLabels`: one machine for all `k` (`∃ alg` comes
before the instance), which halts in polynomial time on every encoded input, and whose output is correct on the instances of the theorem. The paper names no machine; polynomial time on discrete
input does not depend on the reasonable model. -/
theorem theorem_2 :
    ∃ alg : Instance → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encInstance encLabels alg) ∧
        ∀ I : Instance, I.WellFormed → FEAC I.toDG I.termSet I.cap →
          (I.terms.map Prod.snd).sum + I.terms.length = I.n → IsLabelPartition I (alg I) := by sorry

end GyoriLovasz
