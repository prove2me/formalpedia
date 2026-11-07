-- Prove2me | Theorems.Thm_GyoriLovasz_theorem_1
-- name    : GyoriLovasz.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:39.509009+00:00
-- url     : https://prove2.me/theorems/021d7aca-f109-488f-9258-3b945094b4e1
-- title:
--   Theorem 1 — polynomial-time Győri–Lovász partition of a k-T-connected digraph
-- statement:
--   There is a single polynomial-time algorithm with the following property. Let $G=(V,E)$ be a directed graph and $T=\{t_1,\dots,t_k\}$ a set of distinct terminals. Assume that $G$ is $k$-$T$-connected, that is, every non-terminal has $k$ paths to $k$ distinct terminals that share only their start, and let $c_1,\dots,c_k$ be nonnegative integers with
--   $$\sum_{i=1}^k c_i=|V\setminus T|.$$
--   Then on input $(G,T,c)$ the algorithm outputs a partition of $V$ into $V_1,\dots,V_k$ such that
--   $$t_i\in V_i,\qquad |V_i|=c_i+1,\qquad G[V_i]\text{ is connected to } t_i\quad(i\in[k]),$$
--   where $G[V_i]$ connected to $t_i$ means that every vertex of $V_i$ has a directed path to $t_i$ inside $V_i$.
--
--   This is the directed Győri–Lovász theorem made algorithmic: the existence of such partitions is due to Győri (1976, undirected) and Lovász (1977, directed), and before this paper no polynomial-time algorithm was known for $k>4$. The graph is arbitrary: it may have loops and edges leaving terminals, and capacities may be $0$.
--
--   **Formalization Note** The algorithm is a Mathlib multi-tape Turing machine (`Turing.TM2ComputableInPolyTime`) reading the input as the vertex count $n$ in binary, the edge list and the list of pairs $(t_i,c_i)$, and writing one label per vertex. The machine must halt within its polynomial bound on every input; on inputs violating the hypotheses its output is unconstrained.
--
--   Differences from the source:
--
--   - reading: "there exists a polynomial-time algorithm" (no machine model is named) → ∃ alg with Turing.TM2ComputableInPolyTime encInstance encLabels alg: one Mathlib multi-tape Turing machine for all k, with binary numbers and a terminated-word encoding; reason: polynomial time on discrete inputs is the same class in every reasonable model; ∃ alg comes before the instance, so the algorithm is uniform
--   - encoding: an algorithm that works on the instances of the theorem → a total function, computed in polynomial time on every encoded input, and correct on the instances satisfying the hypotheses; reason: Mathlib's notion is total; the hypothesis can be tested in polynomial time by maximum flow and [] returned when it fails, so no instance is gained or lost
--   - encoding: G = (V, E), distinct terminals t_1, …, t_k, capacities c_i, ∑ c_i = |V ∖ T| → an Instance (n, edge list, list of (t_i, c_i)) with WellFormed (endpoints and terminals below n, terminals distinct), and ∑ c_i + k = n; reason: for k distinct terminals among n vertices |V ∖ T| = n − k; repeated edges denote one edge
--   - encoding: the partition V_1, …, V_k → a list of n labels below k, with V_i the vertices labelled i; reason: a labelling is a partition into k indexed parts
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 1, p.5 (restated p.23)

import Mathlib
import Definitions.Def_GyoriLovasz_IsKTConnected
import Definitions.Def_GyoriLovasz_encInstance
import Definitions.Def_GyoriLovasz_IsLabelPartition

namespace GyoriLovasz

/-- **Theorem 1.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 1, p.5 (restated p.23): "Let G = (V, E) be a directed graph and T = {t_1, ..., t_k} be a set of distinct terminals. Assume that G is k-T-connected and let c_1, ..., c_k be
nonnegative integers such that ∑_{i=1}^k c_i = |V \ T|. Then there exists a polynomial-time algorithm that partitions the vertices of the graph into V_1, ..., V_k, such that t_i ∈ V_i, |V_i| = c_i + 1, and the
induced subgraph G[V_i] is connected to t_i."

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with the injective encoders `encInstance` (binary numbers) and `encLabels`: one machine for all `k` (`∃ alg` comes
before the instance), which halts in polynomial time on every encoded input, and whose output is correct on the instances of the theorem. The paper names no machine; polynomial time on discrete
input does not depend on the reasonable model. The capacity hypothesis is written `∑ c_i + k = n`, which is `∑ c_i = |V \ T|` for distinct terminals among the `n` vertices. Capacities may be `0`. -/
theorem theorem_1 :
    ∃ alg : Instance → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encInstance encLabels alg) ∧
        ∀ I : Instance, I.WellFormed → IsKTConnected I.toDG I.termSet →
          (I.terms.map Prod.snd).sum + I.terms.length = I.n → IsLabelPartition I (alg I) := by sorry

end GyoriLovasz
