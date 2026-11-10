-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_lemma_C_1
-- name    : GoodHypotheses.Proper.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:15:56.238075+00:00
-- url     : https://prove2.me/theorems/5df54dbe-4a75-4c5b-a4ce-f2bcd897f7a5
-- title:
--   Lemma C.1 — the weighted λ-quantile of n weighted reals in deterministic O(n) worst-case time
-- statement:
--   Given real values $v_1,\dots,v_n$ with positive weights $w_1,\dots,w_n$ summing to $1$, the smallest input value whose cumulative weight $\sum_{i:v_i\le v_j}w_i$ is at least $\lambda\in[0,1]$ can be found deterministically in $O(n)$ worst-case time: one fixed oracle-free program and one universal constant $C$ such that for every such input the program halts within $Cn+C$ steps with that value in its real output cell.
--
--   Differences from the source:
--
--   - reading: "can be found deterministically in O(n) worst-case time" → ∃ C > 0, ∃ an Admissible OracleFree program that, for every n ≥ 1 and every valid input, halts within C·n + C steps with wQuantile v w λ in real memory cell −1; reason: machine reading of 'time'; the additive C covers the constant overhead
--   - reading: "runs in time", constant-time sampling and density queries (pp. 1–2, §3) → the number of executed instructions of an Admissible program of the unit-cost randomized real RAM `Machine` (SmaleNinth core, integer memory, exp, log, uniform tape, opaque X-registers with sampleP, sampleH, evalH, halt; rational literals, no floor); reason: the paper names no machine; every arithmetic operation and every oracle call costs one unit
--   - encoding: the input v, w, λ → n in integer memory cell 0; λ, v_1..v_n, w_1..w_n in real memory cells 0, 1..n, n+1..2n; reason: input layout
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 37, Lemma C.1

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Proxies
import Definitions.Def_GoodHypotheses_Proper_Machine

namespace GoodHypotheses.Proper

/-- Lemma C.1 (p. 37): one fixed deterministic, oracle-free program and one universal constant
`C` such that, for every `n ≥ 1`, all reals `v_1, …, v_n`, positive weights `w_1, …, w_n` with
`∑ w_i = 1` and every `λ ∈ [0, 1]`, the program halts within `C n + C` steps (worst case) with
the smallest input value whose cumulative weight `∑_{i : v_i ≤ v_j} w_i` is at least `λ` in real
memory cell `-1`. -/
theorem lemma_C_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧ OracleFree P ∧
      ∀ (n : ℕ) (v w : Fin n → ℝ) (lam : ℝ) (ω : Tape Unit n), 1 ≤ n →
        (∀ i, 0 < w i) → ∑ i, w i = 1 → 0 ≤ lam → lam ≤ 1 →
        HaltsWithin P (fun _ _ => 0) ω (quantileInput Unit v w lam) (C * n + C) ∧
        outReal P (fun _ _ => 0) ω (quantileInput Unit v w lam) = wQuantile v w lam := by sorry

end GoodHypotheses.Proper
