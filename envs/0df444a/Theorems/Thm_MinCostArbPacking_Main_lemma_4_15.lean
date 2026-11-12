-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_15
-- name    : MinCostArbPacking.Main.lemma_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:07.848225+00:00
-- url     : https://prove2.me/theorems/f5b7eee5-054d-4b38-b36b-12618374475b
-- title:
--   Lemma 4.15 — restoring a mandatory arc in $O(k^2|T|+k|T|\log|T|)$
-- statement:
--   **Lemma 4.15 (Restoring a mandatory arc).** Let $T$ be a $B$-tight block and $e\in I^{cr}[T]\setminus B$. Given the spanning trees $B[T]=F_1[T]\,\dot\cup\cdots\dot\cup\,F_k[T]$, one can find an arc $f\in B[T]\setminus I^{cr}$ and a decomposition of $B[T]-f+e$ into $k$ spanning trees of $T$ in
--
--   $$O\big(k^2|T|+k|T|\log|T|\big)$$
--
--   time. Formally: one program and an absolute constant $C$ such that, on every block given with its $k$ spanning trees, its mandatory arcs and the missing mandatory arc $e$ (the mandatory arcs together with $e$ being independent), the program outputs such $f$ and decomposition within $C$ times this bound.
--
--   Differences from the source:
--   - encoding: running time $O(f)$ in the model of §3.1 (exact arithmetic and comparisons in constant time) → one program of the unit-cost real RAM `Machine`, chosen before the input, halting within $C\cdot f$ executed instructions with an absolute constant $C$, for every word bound $W \ge (\mathrm{size}+2)^{c}$; reason: the standard reading of a deterministic time bound; the step count is intrinsic to the interpreter
--   - encoding: $e\in I^{cr}[T]$ with $I^{cr}$ independent → the mandatory arcs of $B[T]$ together with $e$ are independent; $T$ relabelled as $\{0,\dots,t-1\}$; reason: these are the properties of $I^{cr}$ the source uses
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.4, p.19, Lemma 4.15

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_IO
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.15 (Restoring a mandatory arc), p.19: let `T` be a `B`-tight block and
`e ∈ I^cr[T] ∖ B`. Given the spanning trees `B[T] = F₁[T] ∪̇ ⋯ ∪̇ F_k[T]`, one program finds an arc
`f ∈ B[T] ∖ I^cr` and a decomposition of `B[T] - f + e` into `k` spanning trees of `T` in
`O(k²|T| + k|T| log |T|)` steps (at most `C` times that, `C` absolute). -/
theorem lemma_4_15 : ∃ (P : Machine.Program) (cw : ℕ) (C : ℝ), ∀ R : RepairInput, 1 ≤ R.k →
    R.Pre → ∀ W : ℤ, ((R.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
      Machine.HaltsWithin P W R.inI []
        (C * ((R.k : ℝ) ^ 2 * R.t + R.k * R.t * logL R.t))
        (fun o _ => RepairOutput R o) := by sorry

end MinCostArbPacking.Main
