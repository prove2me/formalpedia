-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_quartic_query_upper_bound
-- name    : MaxCutMatrix2027.Upper.quartic_query_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T12:49:01.36931+00:00
-- url     : https://prove2.me/theorems/526a3837-176d-48ca-b91b-50ce804f6172
-- title:
--   Theorem 4.1 — Quartic query upper bound with RAM time
-- statement:
--   For every integer $n\ge2$ and every real $0<\varepsilon\le1$, Algorithm 1 is a randomized non-adaptive estimator of MAX-CUT on every simple $n$-vertex graph. It returns a real $\widehat M$ satisfying
--   $$\Pr\{|\widehat M-\operatorname{MAXCUT}(G)|\le\varepsilon n^2\}\ge\frac23.$$
--   There are absolute constants, chosen before all inputs and all random outcomes, for which its worst-case resources obey
--   $$q\le\frac{2(C+1)^2}{\varepsilon^4},\qquad
--   \mathrm{time}\le2^{T/\varepsilon^2},\quad T>0.$$
--   The single sample coefficient is specified by positive absolute $C_{\mathrm{RV}}$, $C_{\mathrm{res}}=2C_{\mathrm{RV}}$, $C_0=(3C_{\mathrm{res}}+29)/4$, and $C=\max(6,144C_0^2)$, with $s=\lceil C/\varepsilon^2\rceil$.
--
--   The formal conclusion requires a trace chosen before the graph, containing exactly the planned increasing pairs without repetition; every graph has a terminating execution of the same fixed program with that trace and the displayed time bound. Its output is the exact full-graph maximum when $n\le s$, zero on overflow, and $n^2\operatorname{MAXCUT}(G[Q])/s^2$ otherwise. The number of random draws is at most $2s+1$ and every draw uses parameter $s/n$. For $s<n$, the implemented geometric-gap output law equals the capped independent-Bernoulli output law. Accuracy is measured on actual terminating executions, not on a separately postulated output distribution.
--
--   **Formalization Note** Time counts operational RAM transitions, including loads, stores, comparisons, query-table construction, binary-array cut enumeration and rescaling. Exact geometric-gap generation, ceiling, index arithmetic and real arithmetic are unit-cost primitives, as in the source's p.28 RAM analysis. This is not a bit-complexity assertion. The graph, randomness, correctness and costs are not supplied as promised fields.
--
--   Differences from the source:
--   - encoding: existence of the tester exhibited by Algorithm 1 with O bounds → the fixed RAM program, its exact output law, graph-independent trace and explicit uniform resource inequalities; reason: these spell out the same algorithm and both source complexity conclusions, rather than assuming accuracy or costs
--   - encoding: RAM sampling in O(s) via geometric gaps without a bit-level instruction set → unit-cost exact geometric-gap generation, arithmetic, ceiling, random-access memory and charged control transitions; reason: this pins down the source RAM convention and makes no bit-complexity claim
--   - encoding: a sufficiently large absolute sample coefficient and 2 to O(1/epsilon squared) time → C=max(6,144 C0 squared) with C0=(3(2 CRV)+29)/4, and an existential positive absolute exponent T; reason: the source proof bounds failure by exp(-C/3)+C0/sqrt(C), which is below one third for this choice
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Theorem 4.1, Algorithm 1, p.17; proof pp.27–28, p.17 (PDF p.17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Algorithm
set_option autoImplicit false
open MeasureTheory
open scoped Classical

namespace MaxCutMatrix2027.Upper

/-- Theorem 4.1, p.17, Algorithm 1, and its RAM implementation on p.28.
The constants precede every instance. Time is the number of RAM transitions.
The trace witness is chosen before the graph, expressing non-adaptivity.
The law identity identifies this implementation with the capped Bernoulli tester. -/
theorem quartic_query_upper_bound :
    ∃ (C_RV T : ℝ), 0 < C_RV ∧ 0 < T ∧
      let C_res := 2 * C_RV
      let C₀ := (3 * C_res + 29) / 4
      let C := max 6 (144 * C₀ ^ 2)
      ∀ (n : ℕ), 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      let s := sampleSize C ε
      (∀ ω : RandomTape (2 * s + 1),
        ∃ pairs : List (ℕ × ℕ),
          pairs.toFinset = plannedPairs n s ω ∧ pairs.Nodup ∧
          (pairs.length : ℝ) ≤ 2 * (C + 1) ^ 2 / ε ^ 4 ∧
          (∀ e ∈ pairs, e.1 < e.2 ∧ e.2 < n) ∧
          ∀ G : SimpleGraph (Fin n), ∃ t : ℕ,
            (t : ℝ) ≤ Real.rpow 2 (T / ε ^ 2) ∧
            (execution G ε C ω t).output = some (algorithmEstimate G s ω) ∧
            (execution G ε C ω t).queries = pairs ∧
            (execution G ε C ω t).randomCursor ≤ 2 * s + 1 ∧
            (∀ p ∈ (execution G ε C ω t).randomParameters, p = (s : ℝ) / n)) ∧
      (∀ G : SimpleGraph (Fin n),
        ENNReal.ofReal ((2 : ℝ) / 3) ≤ gapLaw n s (successEvent G ε C) ∧
        (s < n → ∀ B : Set ℝ,
          gapLaw n s {ω | algorithmEstimate G s ω ∈ B} =
            ENNReal.ofReal (sampleAverage ((s : ℝ) / n)
              (fun Q => if bernoulliEstimate G s Q ∈ B then 1 else 0)))) := by sorry

end MaxCutMatrix2027.Upper
