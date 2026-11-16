-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_B_1
-- name    : GeoQAC.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:30:55.172302+00:00
-- url     : https://prove2.me/theorems/36c7854a-8271-4a64-9946-3e1dd03cdc70
-- title:
--   Theorem B.1 — exactification of approximate clean parity
-- statement:
--   For every $p>1/2$ there is a constant $K_p>0$ such that the following holds. Let $C$ be a depth-$d$ $[n+1,h]$-2D-QAC circuit, $d\ge1$, whose $n+1$ logical qubits (the $n$ controls and the accumulator) fill a boundary column, and which is a $p$-approximate clean implementation of the parity unitary $U_{\oplus n}$. Let $a=(n+1)h-(n+1)$ be its number of ancillas. Then there is an exact clean implementation of $U_{\oplus n}$ by a $[w',h']$-2D-QAC circuit with
--   $$
--   w'\le n+1+K_p,\qquad h'\le h+K_p,\qquad \text{depth}\le K_p\,d,
--   $$
--   and at most $K_p(n+a+1)$ ancillas, its logical qubits at any positions.
--
--   Approximate clean parity synthesis can therefore be made exact at constant-factor cost in depth and constant additive cost in the layout.
--
--   Differences from the source:
--   - encoding: a [w, h] circuit whose logical qubits fill a boundary column → grid Pos (n+1) h with every control and the accumulator in one boundary column c, in any order; reason: n + 1 logical qubits fill a column exactly when it has w = n + 1 rows and contains all of them
--   - encoding: depth d → 1 ≤ d; reason: Appendix B's convention (p.40: "We take the synthesis depth d to be at least one")
--   - reading: the new logical inputs may occupy added boundary positions → the logical qubits of the exact circuit may sit at any positions; reason: the sentence permits a placement and imposes none, so the conclusion only asserts the existence of an exact clean circuit with the stated resources
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem B.1, p.39

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_IsCleanImpl
import Definitions.Def_GeoQAC_Supplement_IsApproxCleanParity

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem B.1** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.39). "For fixed
`p > 1/2`, let `C` be a depth-`d` `[w, h]`-2D-QAC circuit that `p`-approximately implements clean
parity on `n` controls, with its logical qubits filling a boundary column. Then, exact clean parity
on `n` controls has a depth-`O(d)` `[w + O(1), h + O(1)]`-2D-QAC implementation. The new logical
inputs may occupy added boundary positions. If `C` uses `a` ancillas, the exact circuit uses
`O(n + a + 1)` ancillas; the conversion preserves polynomial resources."

**Formalization Note.**
* "For fixed `p`": `∀ p > 1/2 ∃ K_p`. Depth `d ≥ 1` (Appendix B, p.40: "We take the synthesis depth
  `d` to be at least one").
* "Logical qubits filling a boundary column": the `n + 1` logical qubits (controls `ctrl`,
  accumulator `acc`) all lie in one boundary column `c` of a grid with `w = n + 1` rows, so they fill
  it, in any order. `p`-approximate clean implementation is Definition 2.5's squared fidelity on the
  whole output for every logical unit vector (`IsApproxCleanParity`).
* The exact circuit (published `GeoQAC.IsCleanParity`) has `w' ≤ n + 1 + K`, `h' ≤ h + K`,
  depth `≤ K d`, and `w'h' − (n + 1) ≤ K (n + a + 1)` ancillas with `a = (n + 1)h − (n + 1)`; its
  logical qubits may be anywhere. The size bounds give polynomial resources. -/
theorem theorem_B_1 : ∀ p : ℝ, 1 / 2 < p → ∃ K : ℝ, 0 < K ∧
    ∀ (n h d : ℕ) (C : QACCircuit (Pos (n + 1) h) d) (ctrl : Fin n ↪ Pos (n + 1) h)
      (acc : Pos (n + 1) h) (c : Fin h),
      1 ≤ d → C.Is2D → IsBoundaryCol c → (∀ i, (ctrl i).2 = c) → acc.2 = c →
      IsApproxCleanParity p C ctrl acc →
      ∃ (w' h' D : ℕ) (C' : QACCircuit (Pos w' h') D) (ctrl' : Fin n ↪ Pos w' h')
        (acc' : Pos w' h'),
        C'.Is2D ∧ (w' : ℝ) ≤ n + 1 + K ∧ (h' : ℝ) ≤ h + K ∧ (D : ℝ) ≤ K * d ∧
        ((w' * h' : ℕ) : ℝ) - (n + 1) ≤ K * (n + (((n + 1) * h : ℕ) - (n + 1) : ℝ) + 1) ∧
        IsCleanParity C' ctrl' acc' := by sorry

end GeoQAC.Supplement
