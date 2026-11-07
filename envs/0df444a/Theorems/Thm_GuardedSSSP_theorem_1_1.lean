-- Prove2me | Theorems.Thm_GuardedSSSP_theorem_1_1
-- name    : GuardedSSSP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:55.216202+00:00
-- url     : https://prove2.me/theorems/27770fa9-a682-4737-9e17-73db3f77c00a
-- title:
--   Theorem 1.1 — one uniform comparison–addition RAM program solves SSSP in $O(m+n+K\Phi(K)e^{O(\log^*_2(K+2))})$ time, $K=K_{\mathrm{CA}}(G,s)$
-- statement:
--   There exist one finite deterministic program $U_*$ of the graph-input-uniform comparison–addition RAM (with its word exponent) and absolute constants $a,b>0$ such that for every finite directed multigraph $G$ with $n$ vertices and $m$ arcs, every source $s$ and every weighting $w\in\mathbb R^E_{\ge0}$, the program $U_*$ halts on $(G,s,w)$ with the exact labeled distances (an infinity flag for each unreachable vertex and the value $d_w(s,v)$ for each reachable one) within
--
--   $$\mathrm{RAM}_{U_*}(G,s,w)\le a\Big[m+n+K\Phi(K)\exp\big(b\log^*_2(K+2)\big)\Big],\qquad K=K_{\mathrm{CA}}(G,s)$$
--
--   steps. Parallel arcs, loops, zero weights, ties and zero-weight cycles are all allowed.
--
--   The bound is instance-sensitive: it charges the uniform solver, which receives the graph as input, only a near-constant factor $\Phi(K)\exp(O(\log^*_2(K+2)))$ over the optimal cost $K$ of a comparison–addition program specialized to the topology.
--
--   **Formalization Note** The program, its word exponent and $a,b$ are chosen before $n,m,G,s,w$. The source is a vertex, so $n\ge1$.
--
--   Differences from the source:
--   - reading: the guarded-prefix construction gives one … program U∗ → ∃ U : Machine.Program; reason: the construction is how the proof obtains the witness; the theorem asserts its existence
--   - reading: the comparison-addition RAM of section 4 → Machine: two banks, integer + − × ⌊÷⌋ shifts bit length on words bounded by (m+n+2)^c with c chosen with the program, real literal 0, + and three-way comparison only, no casts, unit cost per instruction, the stated input and output layout; reason: §4.1 fixes the instruction kinds but no syntax; this machine is no stronger than the paper's
--   - reading: K_CA(G, s) over finite deterministic programs → KCA over decision trees with real literals (CAProg); reason: see Lemma B.1; trees capture programs with free discrete state
--   - encoding: RAM_{U∗}(G, s, w) ≤ bound → ∃ T with U halted at step T, correct output at that state, and T ≤ bound; reason: a halted state stutters, so this is the first halting time
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Theorem 1.1, p.1 (PDF p.2), display (2)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist
import Definitions.Def_GuardedSSSP_KCA
import Definitions.Def_GuardedSSSP_Machine
import Definitions.Def_GuardedSSSP_LogHierarchy

namespace GuardedSSSP

open AtomicDynRouting.ResidenceTime

/-- **Theorem 1.1** (Uniform maximal-depth bound), p.1 (PDF p.2).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "In the comparison-addition RAM of section 4, the
guarded-prefix construction gives one finite deterministic graph-input-uniform exact SSSP program U∗ and
absolute constants a, b > 0 such that for every finite directed multigraph, source, and independent
nonnegative real weighting, RAM_{U∗}(G, s, w) ≤ a[m + n + KΦ(K) exp(b log∗₂(K + 2))], K = K_CA(G, s). (2)"

There is one program `U` of the comparison–addition RAM (`Machine.Program`, with its word exponent) and
constants `a, b > 0`, all chosen before the input, such that for every `n, m`, every directed multigraph
`G` on `Fin n` with arcs `Fin m`, every source `s` and every weighting `w ≥ 0`, `U` halts within `T` steps
with the exact labeled distances, where `T ≤ a(m + n + KΦ(K)exp(b log*₂(K + 2)))` and `K = K_CA(G, s)`.

**Formalization Note.** "The guarded-prefix construction gives one … program" is read as the existence of
the program; the construction is the proof's witness. Halting is required on every input (a stuck or
non-halting run fails), and the output is read at the halting step: the infinity flag and the value, per
`Machine.OutputCorrect`. `n ≥ 1` because the source is a vertex. Zero weights, ties, loops, parallel arcs
and zero cycles are all allowed. -/
theorem theorem_1_1 :
    ∃ U : Machine.Program, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ (n m : ℕ) (G : Network (Fin n) (Fin m)) (s : Fin n) (w : Fin m → ℝ), (∀ e, 0 ≤ w e) →
        ∃ T : ℕ, Machine.HaltsWithin U G s w T ∧
          Machine.OutputCorrect G s w (Machine.run U G s w T) ∧
          (T : ℝ) ≤ a * ((m : ℝ) + n + (KCA G s : ℝ) * Phi (KCA G s) *
            Real.exp (b * (logStar ((KCA G s : ℝ) + 2) : ℝ))) := by sorry

end GuardedSSSP
