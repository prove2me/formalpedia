-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_16
-- name    : MinCostArbPacking.Main.lemma_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:26.718047+00:00
-- url     : https://prove2.me/theorems/a934ce7e-5d59-4f3d-8303-be616edcfea1
-- title:
--   Lemma 4.16 — Algorithm 2 (Extend) in $O(k^2(|H|+t)\log(kt)+k^3t)$
-- statement:
--   **Lemma 4.16.** Algorithm 2 is correct and runs in
--
--   $$O\big(k^2(|H|+t)\log(kt)+k^3t\big)$$
--
--   time. Here the input is the arc set $H=I^{cr}\,\dot\cup\,A$ of the contracted graph on $t$ vertices, with indegree at most $k$ and $I^{cr}$ independent in $\mathcal G^k$, and the output is a largest independent $K$ with $I^{cr}\subseteq K\subseteq I^{cr}\cup A$ together with a forest decomposition of $K$.
--
--   Formally: one program and an absolute constant $C$ meeting this specification within $C$ times the bound on every such input with $t\ge1$.
--
--   Differences from the source:
--   - encoding: running time $O(f)$ in the model of §3.1 (exact arithmetic and comparisons in constant time) → one program of the unit-cost real RAM `Machine`, chosen before the input, halting within $C\cdot f$ executed instructions with an absolute constant $C$, for every word bound $W \ge (\mathrm{size}+2)^{c}$; reason: the standard reading of a deterministic time bound; the step count is intrinsic to the interpreter
--   - reading: "Algorithm 2 is correct and runs in … time" → some program of the machine meets Algorithm 2's Input/Output specification within the bound; reason: Algorithm 2 calls Lemma 3.6, whose program is itself only asserted to exist, so Algorithm 2 cannot be written as a fixed program
--   - encoding: the contracted graph on $t$ vertices → a digraph with $t\ge1$ vertices; reason: the contracted graph has at least one block
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.4, p.20, Lemma 4.16 (Algorithm 2, p.19)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_IO
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.16, p.20: Algorithm 2 (`Extend(H)`) is correct and runs in
`O(k²(|H| + t) log(kt) + k³ t)` time: one program which, on the contracted graph with `t` vertices,
arc set `H = I^cr ∪̇ A`, indegree at most `k` and `I^cr` independent, returns a largest independent
`K` with `I^cr ⊆ K ⊆ H` together with a forest decomposition, within `C` times that bound (`C`
absolute). -/
theorem lemma_4_16 : ∃ (P : Machine.Program) (cw : ℕ) (C : ℝ), ∀ Z : ExtendInput, 1 ≤ Z.k → 1 ≤ Z.t →
    Z.Pre → ∀ W : ℤ, ((Z.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
      Machine.HaltsWithin P W Z.inI []
        (C * ((Z.k : ℝ) ^ 2 * (Z.h + Z.t) * logL ((Z.k : ℝ) * Z.t) + (Z.k : ℝ) ^ 3 * Z.t))
        (fun o _ => ExtendOutput Z o) := by sorry

end MinCostArbPacking.Main
