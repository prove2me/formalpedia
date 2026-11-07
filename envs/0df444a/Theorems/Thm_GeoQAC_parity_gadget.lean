-- Prove2me | Theorems.Thm_GeoQAC_parity_gadget
-- name    : GeoQAC.parity_gadget
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:20.34242+00:00
-- url     : https://prove2.me/theorems/1cc4c4ec-475a-43f3-8fea-0b13c824c00a
-- title:
--   Proof of Theorem 4.1(d), p.31 — the constant-depth $[O(m),\exp(O(m\log m))]$ clean parity gadget
-- statement:
--   There is an absolute constant $C_2$ such that for every $m\ge2$ there is a clean parity implementation on $m$ controls by a $[w,h]$-2D-QAC circuit of depth at most $C_2$ with
--   $$
--   w\le C_2\,m,\qquad h\le\exp(C_2\,m\log m).
--   $$
--   Its inputs lie in the left boundary column and its accumulator at the right end of the top row, which contains no input.
--
--   In the paper: "We first give a constant-depth $[O(m),\ell_m]$-2D-QAC clean parity gadget on $m$ controls, where $\ell_m=\exp(O(m\log m))$. … Its inputs form a left boundary column, its workspace is to the right of that column, and its accumulator can be placed in an additional top row at the right boundary. Enlarging the constants accommodates the finitely many small values of $m$." The gadget is the building block of the recursive construction of Theorem 4.1(d), which uses it with $m=\lceil n^{1/d}\rceil\ge2$.
--
--   Differences from the source:
--   - encoding: $[O(m),\exp(O(m\log m))]$, constant depth → one absolute $C_2$ with $w\le C_2m$, $h\le\exp(C_2m\log m)$, depth $\le C_2$, natural logarithm, for every $m\ge2$; reason: §2.1, p.9, and "Enlarging the constants accommodates the finitely many small values of $m$".
--   - encoding: "inputs form a left boundary column … accumulator in an additional top row at the right boundary" → every control is in column $0$ and not in row $0$, and the accumulator is at (row $0$, column $h-1$); reason: the placement sentence of the proof; the workspace clause is implied by the clean-implementation condition.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), proof of Theorem 4.1(d), p.31

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_IsCleanImpl

namespace GeoQAC

/-- **The clean parity gadget** (proof of Theorem 4.1(d), arXiv:2604.07178, version of 2026-11-03,
p.31). "We first give a constant-depth `[O(m), ℓ_m]`-2D-QAC clean parity gadget on `m` controls,
where `ℓ_m = exp(O(m log m))`. … Its inputs form a left boundary column, its workspace is to the
right of that column, and its accumulator can be placed in an additional top row at the right
boundary. Enlarging the constants accommodates the finitely many small values of `m`."

**Formalization Note.**
* One absolute constant `C₂` bounds the width by `C₂ m`, the length by `exp(C₂ m log m)` and the depth
  by `C₂`, for every `m ≥ 2` (the gadget is used with `m = ⌈n^{1/d}⌉ ≥ 2`).
* Placement: every control lies in column `0` and not in row `0`; the accumulator is at the right end
  `(0, h − 1)` of the top row `0`, which holds no control. -/
theorem parity_gadget : ∃ C₂ : ℝ, ∀ m : ℕ, 2 ≤ m →
    ∃ (w h D : ℕ) (C : QACCircuit (Pos w h) D) (ctrl : Fin m ↪ Pos w h) (acc : Pos w h),
      C.Is2D ∧ (w : ℝ) ≤ C₂ * m ∧ (h : ℝ) ≤ Real.exp (C₂ * m * Real.log m) ∧ (D : ℝ) ≤ C₂ ∧
      IsCleanParity C ctrl acc ∧
      (∀ i, (ctrl i).2.val = 0 ∧ 0 < (ctrl i).1.val) ∧ acc.1.val = 0 ∧ acc.2.val + 1 = h := by sorry

end GeoQAC
