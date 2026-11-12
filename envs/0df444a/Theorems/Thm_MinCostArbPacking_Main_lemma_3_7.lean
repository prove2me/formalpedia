-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_3_7
-- name    : MinCostArbPacking.Main.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:08.207202+00:00
-- url     : https://prove2.me/theorems/d7f22c7a-1bc2-4202-9043-1861b8ac3f32
-- title:
--   Lemma 3.7 — arborescence extraction in $O(km\log n+k^4n\log^2 n)$ [BHKP08]
-- statement:
--   **Lemma 3.7** (Arborescence extraction; [BHKP08, Theorem 1.4], cited). If an unweighted digraph contains $k$ arc-disjoint $r$-arborescences, then one finds $k$ such arborescences deterministically in
--
--   $$O\big(km\log n+k^4n\log^2 n\big)$$
--
--   time. Formally: one program and an absolute constant $C$ such that on every digraph (loops and parallel arcs allowed) containing such a packing, the program halts within $C$ times this bound and outputs a packing.
--
--   It is the final step of Algorithm 1.
--
--   Differences from the source:
--   - encoding: running time $O(f)$ in the model of §3.1 (exact arithmetic and comparisons in constant time) → one program of the unit-cost real RAM `Machine`, chosen before the input, halting within $C\cdot f$ executed instructions with an absolute constant $C$, for every word bound $W \ge (\mathrm{size}+2)^{c}$; reason: the standard reading of a deterministic time bound; the step count is intrinsic to the interpreter
--   - encoding: an unweighted digraph → an `Instance` whose cost field is ignored (input without costs); reason: costs do not enter the input or the output condition
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.4, p.9, Lemma 3.7 (cited: Bhalgat–Hariharan–Kavitha–Panigrahi 2008, Thm 1.4)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_IO
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 3.7 (Arborescence extraction; [BHKP08, Theorem 1.4]), p.9: if an unweighted digraph
contains `k` arc-disjoint `r`-arborescences, one program finds `k` such arborescences
deterministically in `O(km log n + k⁴ n log² n)` steps (at most `C` times that, `C` absolute). The
input uses the layout of Theorem 1.1 without costs; the cost field of the instance is ignored. -/
theorem lemma_3_7 : ∃ (P : Machine.Program) (cw : ℕ) (C : ℝ), ∀ X : Instance, 1 ≤ X.k →
    X.HasPacking → ∀ W : ℤ, ((X.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
      Machine.HaltsWithin P W X.inI []
        (C * ((X.k : ℝ) * X.m * logL X.n + (X.k : ℝ) ^ 4 * X.n * logL X.n ^ 2))
        (fun o _ => ExtractionOutput X o) := by sorry

end MinCostArbPacking.Main
