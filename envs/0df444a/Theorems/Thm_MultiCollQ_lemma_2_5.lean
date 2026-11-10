-- Prove2me | Theorems.Thm_MultiCollQ_lemma_2_5
-- name    : MultiCollQ.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:20.130215+00:00
-- url     : https://prove2.me/theorems/032adff6-427a-4864-943a-0ae449872cf7
-- title:
--   Lemma 2.5 — output witnesses: $\sqrt p\le\sqrt{p_{\mathrm{db}}}+L\sqrt{2/(N-T)}+\delta_N(T+L)$
-- statement:
--   Let $B$ be an increasing property of partial injections of $[N]$: $D\in B$ and $D\subseteq D'$ imply $D'\in B$. Consider a forward permutation-query algorithm making $T$ forward swap queries whose final measurement outputs at most $L$ input–output pairs. Let $p$ be the probability, for a uniformly random permutation, that the pairs agree with the permutation and form a partial injection in $B$, and let $p_{\mathrm{db}}$ be the probability that the final database after the same $T$ compressed queries belongs to $B$. If $N\ge3$ and $3(T+L)-1\le N$, then
--
--   $$
--   \sqrt p\le\sqrt{p_{\mathrm{db}}}+L\sqrt{\frac{2}{N-T}}+\delta_N(T+L).
--   $$
--
--   This is the permutation analogue of Zhandry's recording lemma: success of the real algorithm forces a witness in the compressed database, up to additive errors.
--
--   **Formalization Note** The algorithm is any `FwdAlg` (finite auxiliary register, unit initial state); its output map sends basis states of the accessible registers to lists of length at most $L$.
--
--   Differences from the source:
--   - encoding: $3(T+L)-1\le N$ → `3 * (T + L) ≤ N + 1`; reason: same condition in natural numbers
--   - encoding: the pairs, after removing duplicates, form a partial injection in $B$ → the restriction of the permutation to the listed inputs lies in $B$ (given that every pair agrees with it); reason: pairs that agree with a permutation form exactly that partial injection
--   - encoding: $D\subseteq D'$ → the graph of $D$ is contained in the graph of $D'$; reason: inclusion of partial injections
--   - encoding: the algorithm models (start state and unitaries independent of the oracle, measurement of the output register) → `FwdAlg` with $U_0$ absorbed into the initial state, computational-basis measurement of the accessible registers and an output map; reason: deferred measurement and purification; same class of algorithms
--   - encoding: $[N]$ → `Fin N` (0-based); reason: Lean convention; same instances
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Lemma 2.5, p.13 (Carolan–Majenz, Lemma 5.1)

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_deltaN
import Definitions.Def_MultiCollQ_FwdAlg

namespace MultiCollQ

open CompPermOracle

/-- Lemma 2.5 (Output witnesses [CM26, Lemma 5.1]) (Peng, Hou, Dong, manuscript (Oct. 2026), p.13).
Let `B` be an increasing property of partial injections. An algorithm making `T` forward swap
queries outputs at most `L` input–output pairs; `p` is the probability that the pairs agree with the
real (uniformly random) permutation and form a partial injection in `B`, and `p_db` the probability
that the final database after the same `T` compressed queries belongs to `B`. If `N ≥ 3` and
`3(T + L) − 1 ≤ N`, then `√p ≤ √p_db + L √(2/(N − T)) + δ_N(T + L)` (2.7).

**Formalization Note.** `3(T + L) − 1 ≤ N` is written `3(T + L) ≤ N + 1`. "Increasing" (`D ∈ B`
and `D ⊆ D′` imply `D′ ∈ B`) has `D ⊆ D′` as inclusion of graphs. The output is read by measuring
the accessible registers in the computational basis and applying `out`; the pairs agreeing with
`π` form the partial injection `π|_{inputs listed}` (`pairsPInj`). The algorithm class is
`FwdAlg`: arbitrary finite auxiliary registers, arbitrary initial unit vector, forward queries
only. -/
theorem lemma_2_5 {N T L : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk] (hN : 3 ≤ N)
    (hTL : 3 * (T + L) ≤ N + 1) (A : FwdAlg N Wk) (out : FAcc N Wk → List (Fin N × Fin N))
    (hout : ∀ c, (out c).length ≤ L) (B : Set (PartialPerm N))
    (hB : ∀ D D' : PartialPerm N, D ∈ B → (∀ x y, D x = some y → D' x = some y) → D' ∈ B) :
    Real.sqrt (A.witnessProb T out B) ≤
      Real.sqrt (A.dbProb T B) + (L : ℝ) * Real.sqrt (2 / ((N : ℝ) - T)) + deltaN N (T + L) := by sorry

end MultiCollQ
