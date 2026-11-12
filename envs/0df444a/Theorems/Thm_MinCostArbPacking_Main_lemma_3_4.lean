-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_3_4
-- name    : MinCostArbPacking.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:07.115437+00:00
-- url     : https://prove2.me/theorems/94fbb729-7c89-4328-9177-4d61f85cc1dd
-- title:
--   Lemma 3.4 — computing the tight blocks in $O(kn\log n)$ [GW92]
-- statement:
--   **Lemma 3.4** (Computing tight blocks [GW92, Theorem 5.4]; see [AK26, Lemma 4.4], cited). Given a forest decomposition of $I$, the partition $\mathcal T(I)$ can be computed deterministically in
--
--   $$O(kn\log n)$$
--
--   time. Formally: there are a program of the real RAM and an absolute constant $C$ such that, on every arc set $I$ on $n\ge1$ vertices given with a decomposition into $k$ forests, the program halts within $C\,k\,n\log n$ steps and labels the vertices so that two vertices get equal labels exactly when they lie in the same tight block.
--
--   It is used once per phase.
--
--   Differences from the source:
--   - encoding: running time $O(f)$ in the model of §3.1 (exact arithmetic and comparisons in constant time) → one program of the unit-cost real RAM `Machine`, chosen before the input, halting within $C\cdot f$ executed instructions with an absolute constant $C$, for every word bound $W \ge (\mathrm{size}+2)^{c}$; reason: the standard reading of a deterministic time bound; the step count is intrinsic to the interpreter
--   - encoding: the input graph → the arc set $I$ itself with its forest labels, on $n\ge1$ vertices; reason: only $I$ determines $\mathcal T(I)$; $n\ge1$ excludes the empty instance on which $O(0)$ time is meaningless
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.2, p.8, Lemma 3.4 (cited: Gabow–Westermann 1992, Thm 5.4; Arkhipov–Kolmogorov 2026, Lemma 4.4)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_IO
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 3.4 (Computing tight blocks [GW92, Theorem 5.4]; see [AK26, Lemma 4.4]), p.8: given a
forest decomposition of `I`, the partition `𝒯(I)` can be computed deterministically in
`O(kn log n)` time: one program, for every input, at most `C·k·n·log n` steps for an absolute
constant `C`. The input is the arc set `I` (all input arcs) on `n` vertices with its forest labels;
the output labels vertices so that two vertices get equal labels iff they lie in the same tight
block. -/
theorem lemma_3_4 : ∃ (P : Machine.Program) (cw : ℕ) (C : ℝ), ∀ Y : LabelledInput, 1 ≤ Y.k → 1 ≤ Y.n →
    (∀ i, Y.G.IsForest (Y.F i)) →
    ∀ W : ℤ, ((Y.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
      Machine.HaltsWithin P W Y.inI [] (C * (Y.k * Y.n * logL Y.n))
        (fun o _ => TightBlocksOutput Y o) := by sorry

end MinCostArbPacking.Main
