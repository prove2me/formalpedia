-- Prove2me | Theorems.Thm_MantriCVQ_Supplement_theorem_1_3
-- name    : MantriCVQ.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:07:37.122593+00:00
-- url     : https://prove2.me/theorems/b661b026-a4a6-4530-aa68-3efc40365806
-- title:
--   Theorem 1.3 — for every height function $h$, a unary $L_h\in\mathsf{EQP}^{O_h}\setminus\mathsf{PH}^{O_h}$ with $3^{h(n)}$ quantum queries and a $2h(n)$-message public-coin proof
-- statement:
--   Let $h$ be a height function. There are a classical Boolean oracle $O_h$ and a total unary language $L_h$ with
--   $$L_h\in\mathsf{EQP}^{O_h}\quad\text{and}\quad L_h\notin\mathsf{PH}^{O_h},$$
--   and with the following bounds on input $1^n$.
--
--   1. A uniform quantum algorithm decides $L_h$ exactly with $3^{h(n)}$ queries and in time $3^{h(n)}\,\mathrm{poly}(n)$.
--   2. $L_h$ has a public-coin interactive proof system relative to $O_h$ with perfect completeness and soundness error at most $1/4$ against computationally unbounded provers, in which the verifier and the prover exchange $2h(n)$ messages, $h(n)$ from each party. The prover sends fewer than $n\cdot4^{h(n)}/3$ bits in total and the verifier fewer than $n\cdot4^{h(n)}$ random bits. The verifier makes at most $4^{h(n)}$ queries and runs in time $4^{h(n)}\,\mathrm{poly}(n)$.
--   3. The honest prover is a uniform quantum algorithm that makes $4^{h(n)}-3^{h(n)}$ queries and runs in time $4^{h(n)}\,\mathrm{poly}(n)$.
--
--   The published goal (Theorem 1.1) is the case $h=h_{\max}$. Since the height may grow arbitrarily slowly, the theorem gives separations with arbitrarily slowly growing numbers of messages and queries (Corollaries 1.4 and 1.5).
--
--   **Formalization Note** The conclusion is the predicate `HeightBounds h O L`, shared with Theorem 1.6.
--
--   Differences from the source:
--   - generalization: a fixed finite inverse-closed gate set containing H, NOT and Toffoli → the gate set {H, X, Toffoli} for the algorithm and the honest prover; reason: it is contained in every admissible gate set, so the Lean statement implies the paper's for every choice (as in the published goal)
--   - reading: L_h ∉ PH^{O_h}, PH defined with deterministic polynomial-time oracle machines → PH O admits machines that halt within a polynomial clock for this O only; reason: this enlarges PH^O, so L ∉ PH O is the stronger statement (as in the published goal)
--   - generalization: soundness against computationally unbounded provers, classical or quantum, that communicate classically → soundness against every map from input and transcript to a distribution on the next message; reason: every such prover induces these conditional laws, so the class of strategies contains all of them
--   - reading: the honest prover is a uniform polynomial-time quantum algorithm → a memoryless uniform polynomial-size QProver over {H, X, Toffoli}, one circuit per slot, measured; reason: a special case, so its existence is stronger; the paper's prover has this form (as in the published goal)
--   - reading: with 3^{h(n)} queries; makes 4^{h(n)} − 3^{h(n)} queries → exactly 3^{h(n)} oracle gates in the circuit for length n; exactly 4^{h(n)} − 3^{h(n)} oracle gates summed over the prover's slots along every transcript of the schedule; reason: the equality reading of the base mission's Theorems 5.1 and 5.5; it is the stronger reading
--   - encoding: time 3^{h(n)} poly(n) and 4^{h(n)} poly(n) → circuit size and ancilla count at most 3^{h(n)} p(n); verifier decision machine halts within 4^{h(n)} p(n) steps with the oracle O; prover circuit sizes summed at most 4^{h(n)} p(n); one polynomial p; reason: the base mission's convention for time; the oracle-free schedule is polynomial-time by PCVerifier
--   - encoding: 2h(n) messages, h(n) from each party; fewer than n·4^{h(n)}/3 prover bits and n·4^{h(n)} verifier random bits → V.S(1^n) = 2h(n) alternating slots; sums of the lengths of the prover's and of the verifier's slots, compared in ℝ; reason: §3.1 counts every slot as a message; alternation gives h(n) slots to each party; messages have their slot's length
--   - encoding: a total unary language; bounds on input 1^n → L ⊆ range of unary; every bound for n ≥ 1; reason: the paper's domain of n is the positive integers, and there is no promise
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 1.3, pp. 3–4 (PDF pp. 5–6); proof in §7.2, pp. 39–40 (PDF pp. 41–42)

import Mathlib
import Definitions.Def_MantriCVQ_Supplement_HeightFunction
import Definitions.Def_MantriCVQ_Supplement_HeightBounds

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ.Supplement

open MantriCVQ

/-- **Theorem 1.3** (Resource bounds by recursion height; Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), Theorem 1.3, pp. 3–4 (PDF pp. 5–6)): for every height function `h` there are a
classical Boolean oracle `O_h` and a total unary language `L_h` with `L_h ∈ EQP^{O_h}` and
`L_h ∉ PH^{O_h}`, and with the bounds (i)–(iii) on input `1^n` bundled in `HeightBounds`: an exact
uniform quantum algorithm with `3^{h(n)}` queries and time `3^{h(n)} poly(n)`; a public-coin proof with
perfect completeness, soundness error at most `1/4`, `2h(n)` messages (`h(n)` from each party), fewer
than `n · 4^{h(n)}/3` prover bits and `n · 4^{h(n)}` verifier random bits, at most `4^{h(n)}` verifier
queries and verifier time `4^{h(n)} poly(n)`; and a uniform quantum honest prover making
`4^{h(n)} − 3^{h(n)}` queries in time `4^{h(n)} poly(n)`.

**Formalization Note** The conventions (gate set `{H, X, Toffoli}`, exact query counts, time as
circuit size and as step count of the decision machine, slots as messages) are those of
`HeightBounds`; `PH O` admits machines polynomial-time for this `O` only, so `L ∉ PH O` is the
stronger statement. -/
theorem theorem_1_3 (h : ℕ → ℕ) (hh : HeightFunction h) :
    ∃ (O : Oracle) (L : Set Str), HeightBounds h O L := by sorry

end MantriCVQ.Supplement
