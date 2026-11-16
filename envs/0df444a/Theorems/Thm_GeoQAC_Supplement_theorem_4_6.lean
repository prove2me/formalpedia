-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_4_6
-- name    : GeoQAC.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:27:58.770372+00:00
-- url     : https://prove2.me/theorems/72fefc52-020c-4fae-827e-33708512ec69
-- title:
--   Theorem 4.6 — exact clean 1D MAJORITY and MOD at depth $O(n)$
-- statement:
--   1. There is a constant $C_0>0$ such that for every $n\ge2$ there is an exact clean implementation of $U_{\mathrm{MAJ}_n}$ by a $[1,h]$-2D-QAC (1D-QAC) circuit with $h\le n+1+C_0\log n$, that is at most $C_0\log n$ ancillas, and depth at most $C_0n$.
--   2. For every fixed modulus $r\ge2$ there is a constant $C_r>0$ such that for every $n\ge2$ there is an exact clean implementation of $U_{\mathrm{MOD}_{r,n}}$ by a 1D-QAC circuit with $h\le n+1+C_r$ (at most $C_r$ ancillas) and depth at most $C_rn$.
--
--   These match the linear depth lower bounds of Theorem 3.23.
--
--   Differences from the source:
--   - reading: depth O(n) with O(log n) resp. O(1) ancillas (no range of n stated) → explicit bounds for every n ≥ 2, the MOD constant depending on the fixed modulus r; reason: the O(·) constants absorb the finitely many small n; dependence on the fixed parameter r is allowed (§2.1)
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 4.6, p.32

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_IsCleanImpl
import Definitions.Def_GeoQAC_Supplement_hammingWeight

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 4.6** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.32). "The MAJORITY and
fixed-modulus MOD unitaries admit exact clean depth-`O(n)` 1D-QAC synthesis with `O(log n)` and
`O(1)` ancillas, respectively."

**Formalization Note.**
* A 1D-QAC circuit is a `[1, h]`-2D-QAC circuit; it has `n + 1` logical qubits, so `h − (n + 1)` is
  the number of ancillas. Exact clean implementation is the published `GeoQAC.IsCleanImpl`
  (ancillas `|0⟩` in and out, logical qubits anywhere on the line).
* MAJORITY: one absolute `C₀` with `h ≤ n + 1 + C₀ log n` and depth `≤ C₀ n`. MOD: for each fixed
  modulus `r ≥ 2`, a constant `C_r` with `h ≤ n + 1 + C_r` and depth `≤ C_r n`. Both bounds are
  stated for every `n ≥ 2` (the `O(·)` constants absorb the finitely many small `n`). -/
theorem theorem_4_6 :
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ (h D : ℕ) (C : QACCircuit (Pos 1 h) D) (ctrl : Fin n ↪ Pos 1 h) (acc : Pos 1 h),
        C.Is2D ∧ (h : ℝ) ≤ n + 1 + C₀ * Real.log n ∧ (D : ℝ) ≤ C₀ * n ∧
        IsCleanImpl C ctrl acc (majFn n)) ∧
    (∀ r : ℕ, 2 ≤ r → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ (h D : ℕ) (C : QACCircuit (Pos 1 h) D) (ctrl : Fin n ↪ Pos 1 h) (acc : Pos 1 h),
        C.Is2D ∧ (h : ℝ) ≤ n + 1 + C₀ ∧ (D : ℝ) ≤ C₀ * n ∧
        IsCleanImpl C ctrl acc (modFn r n)) := by sorry

end GeoQAC.Supplement
