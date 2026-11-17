-- Prove2me | Theorems.Thm_LinSSWorst_Supplement_theorem_7_1
-- name    : LinSSWorst.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:50:13.50503+00:00
-- url     : https://prove2.me/theorems/e1ab0744-b04e-463a-8d22-19f7af68dd2b
-- title:
--   Theorem 7.1 (Monotone span programs over all fields, = Theorem 1.8) — almost all access structures need MSP size $\ge2^{n/2}/n^{3/4+\varepsilon}$ over every field
-- statement:
--   For every constant $\varepsilon>0$, let $A_n$ be the set of $n$-party access structures $f$ such that every monotone span program computing $f$, over every field (finite or infinite, chosen separately for each $f$), has size at least
--   $$\frac{2^{n/2}}{n^{3/4+\varepsilon}}.$$
--   Then the fraction of $n$-party access structures that lie in $A_n$ tends to one as $n\to\infty$.
--
--   By the equivalence of monotone span programs over finite fields with linear secret sharing [KW93], almost all access structures need linear schemes with total share length $2^{n/2-o(n)}$ over every finite field, which matches the upper bound of Theorem 1.1.
--
--   **Formalization Note** The field ranges over all fields in a universe `Type u` (the statement holds at every universe level); counting is by `Set.ncard`.
--
--   Differences from the source:
--   - encoding: over every field, finite or infinite, chosen separately for each access structure → ∀ (K : Type u) [Field K] inside the counted predicate, universe-polymorphic; reason: quantifying inside the predicate lets the field depend on f; every universe level is covered
--   - encoding: 2^{n/2}/n^{3/4+ε} = 2^{n/2−o(n)} → the explicit bound 2^{n/2}/n^{3/4+ε} (real powers); reason: the equality with 2^{n/2−o(n)} is arithmetic; the explicit form is the stronger one printed
--   - encoding: "almost all": the fraction tends to one → Tendsto (ncard A_n / ncard {access structures}) atTop (𝓝 1); reason: as defined on p.22
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 7.1, p.22; Definition 7.2, p.23; Theorem 1.8, p.6

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_Supplement_MSP

open Filter Topology

namespace LinSSWorst.Supplement

universe u

/-- **Theorem 7.1 (Monotone span programs over all fields)** (= Theorem 1.8, p.6), p.22, from O. Nir,
*Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of
2026-11-02, sha256 5521cfdb…). For every constant `ε > 0`, almost all `n`-party access structures require
monotone span programs of size at least `2^{n/2} / n^{3/4+ε}` over every field, even if the field is chosen
separately for each access structure and may be finite or infinite: the fraction of `n`-party access
structures `f` such that every monotone span program computing `f`, over every field, has at least
`2^{n/2} / n^{3/4+ε}` rows tends to one as `n → ∞`.

**Formalization Note.** Access structures are `IsAccessStructure` (Definition A.1); monotone span programs
are Definition 7.2 (`MSP K n`, size `d`, target `v ≠ 0`, computing `f` means accepting exactly the `A` with
`f(A) = 1`). The field `K` ranges over every field in the universe `Type u` (the statement holds for every
universe level); quantifying `K` inside the counted predicate lets the field depend on `f`. Counting is
`Set.ncard`; the ratio is a real number, and "tends to one" is `Tendsto … atTop (𝓝 1)`. The explicit bound
`2^{n/2} / n^{3/4+ε}` (real powers) is stated, not its `2^{n/2 − o(n)}` form. -/
theorem theorem_7_1 (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((Set.ncard {f : (Fin n → Bool) → Bool | IsAccessStructure f ∧
          ∀ (K : Type u) [Field K] (P : MSP K n), P.Computes f →
            (2 : ℝ) ^ ((n : ℝ) / 2) / (n : ℝ) ^ ((3 : ℝ) / 4 + ε) ≤ (P.d : ℝ)} : ℕ) : ℝ) /
        ((Set.ncard {f : (Fin n → Bool) → Bool | IsAccessStructure f} : ℕ) : ℝ))
      atTop (𝓝 1) := by sorry

end LinSSWorst.Supplement
