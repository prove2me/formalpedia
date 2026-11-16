-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_max2csp_quartic_upper_bound
-- name    : MaxCutMatrix2027.Upper.Supplement.max2csp_quartic_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:12:59.63276+00:00
-- url     : https://prove2.me/theorems/945bc517-8770-444c-bfe9-f198168c8ca7
-- title:
--   Theorem A.1 (companion theorem) — Quartic query upper bound for MAX-2CSP with RAM time
-- statement:
--   There are absolute constants $C,K,T>0$ and one fixed finite program of the mission's unit-cost RAM, chosen before all inputs, such that for every integer $n\ge2$ and every real $0<\varepsilon\le1$ the following hold, with $s=\lceil C/\varepsilon^2\rceil$ and random tape of $2s+1$ independent geometric gaps with parameter $s/n$.
--
--   1. **Non-adaptive queries.** For every tape there is a list of distinct pairs $(u,v)$, $u<v<n$, of length at most $K/\varepsilon^4$, fixed before the instance, such that on every MAX-2CSP instance $F$ the run queries exactly these pairs.
--   2. **Time.** On every tape and instance the run halts within $2^{T/\varepsilon^2}$ transitions, reads at most $2s+1$ gaps and uses only parameter $s/n$.
--   3. **Accuracy.** For every instance $F$,
--   $$\Pr\bigl(|\widehat M-\mathrm{OPT}(F)|\le\varepsilon n^2\bigr)\ge\frac23 .$$
--
--   Each pair query returns the whole set of constraints on the pair. This is the MAX-2CSP counterpart of the mission's goal; Algorithm 2 with the analysis of Theorem A.2 realizes it.
--
--   **Formalization Note** Time counts RAM transitions; geometric-gap generation, ceiling, index and real arithmetic and memory access are unit cost, as in the RAM convention of p.28. No optimum primitive exists: the program must enumerate assignments and evaluate the returned truth-table masks with charged instructions.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: a randomized non-adaptive algorithm whose running time is 2^{O(1/ε²)} in the RAM model, with O(1/ε⁴) pair queries → a fixed finite program of the published unit-cost RAM whose query instruction returns the 16-bit truth-table mask, a tape-dependent query list fixed before the instance, explicit absolute constants K, T with ≤ K/ε⁴ distinct queries and ≤ 2^{T/ε²} transitions; reason: this is the RAM convention of the mission (p.28) and the definitions of worst-case query count and O
--   - encoding: the algorithm's internal randomness → 2s+1 independent geometric(s/n) gaps read by the unit-cost gap instruction, s = ⌈C/ε²⌉; reason: this is the source's own sampling implementation (p.28), used by Algorithm 2 exactly as by Algorithm 1
--   - encoding: constraints (f,u,v) with f:{0,1}²→{0,1} → triples (f,u,v) over Bool with u < v in Fin n, stored as a Finset; reason: Bool encodes {0,1}; a set has no repeated triples, as in §3
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Theorem A.1, p.42 (PDF p.42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_CSP
import Definitions.Def_MaxCutMatrix2027_Upper_Algorithm
set_option autoImplicit false
open MeasureTheory

namespace MaxCutMatrix2027.Upper.Supplement

/-- Theorem A.1, p.42 (Algorithm 2; RAM convention of p.28). There are absolute constants and one
fixed finite RAM program, chosen before `n` and `ε`, such that for every `n ≥ 2` and `0 < ε ≤ 1`:
on every random tape the queried pairs are fixed before any answer (the list `pairs` is chosen
before the instance), are distinct valid pairs `u < v < n`, and number at most `K/ε⁴`; on every
instance the run halts within `2^{T/ε²}` transitions; and the output is within `ε n²` of
`OPT(F)` with probability at least `2/3` over the tape. The tape consists of `2s + 1` independent
geometric gaps with parameter `s/n`, `s = ⌈C/ε²⌉`, read by the unit-cost `gap` instruction. -/
theorem max2csp_quartic_upper_bound :
    ∃ (C K T : ℝ) (prog : List Command), 0 < C ∧ 0 < K ∧ 0 < T ∧
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      let s := sampleSize C ε
      (∀ ω : RandomTape (2 * s + 1),
        ∃ pairs : List (ℕ × ℕ),
          pairs.Nodup ∧ (pairs.length : ℝ) ≤ K / ε ^ 4 ∧
          (∀ e ∈ pairs, e.1 < e.2 ∧ e.2 < n) ∧
          ∀ F : CSPInstance n, ∃ t : ℕ,
            (t : ℝ) ≤ Real.rpow 2 (T / ε ^ 2) ∧
            (cspRun (pairMask F) ω (cspInitial prog n ε) t).output.isSome ∧
            (cspRun (pairMask F) ω (cspInitial prog n ε) t).queries = pairs ∧
            (cspRun (pairMask F) ω (cspInitial prog n ε) t).randomCursor ≤ 2 * s + 1 ∧
            (∀ p ∈ (cspRun (pairMask F) ω (cspInitial prog n ε) t).randomParameters,
              p = (s : ℝ) / n)) ∧
      (∀ F : CSPInstance n,
        ENNReal.ofReal ((2 : ℝ) / 3) ≤ gapLaw n s
          {ω | ∃ t z, (cspRun (pairMask F) ω (cspInitial prog n ε) t).output = some z ∧
            |z - F.optR| ≤ ε * (n : ℝ) ^ 2}) := by sorry

end MaxCutMatrix2027.Upper.Supplement
