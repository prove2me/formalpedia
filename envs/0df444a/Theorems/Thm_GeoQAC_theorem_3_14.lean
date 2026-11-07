-- Prove2me | Theorems.Thm_GeoQAC_theorem_3_14
-- name    : GeoQAC.theorem_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:04.817799+00:00
-- url     : https://prove2.me/theorems/48707595-961a-4a5f-afbe-5da804f7a386
-- title:
--   Theorem 3.14 — $\mathrm{as}(f)\le K^d\sqrt n\,w^{3d+1/2}$ for exact 2D-QAC computation
-- statement:
--   Suppose a depth-$d$, width-$w$ 2D-QAC circuit computes $f:\{0,1\}^n\to\{0,1\}$ exactly from product ancillas. Then
--   $$
--   \mathrm{as}(f)\le K^d\cdot\sqrt n\cdot w^{3d+1/2},
--   $$
--   with the constant $K$ of Theorem 3.7. For $d\ge1$, this implies
--   $$
--   w=\Omega\Big(\big(\mathrm{as}(f)^2/n\big)^{1/(6d+1)}\Big).
--   $$
--   The implicit constant is absolute and independent of $d$.
--
--   The inputs may sit at any positions of the grid, the output at any qubit, and the ancillas may start in any product state.
--
--   Differences from the source:
--   - encoding: "the same constant $K$" as Theorem 3.7 → one existential $K\ge2$ for which Theorem 3.7's bound and the average-sensitivity bound are both stated; reason: separate items cannot share an existential constant.
--   - encoding: $\Omega(\cdot)$ with an absolute constant independent of $d$ → $\exists c>0$, chosen before $d$, with $c\,(\mathrm{as}(f)^2/n)^{1/(6d+1)}\le w$; reason: the theorem's last sentence.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.14, p.25

import Mathlib
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_lmv
import Definitions.Def_GeoQAC_ComputesExactly
import Definitions.Def_GeoQAC_avgSens

namespace GeoQAC

open ObliviousRSP (pureState)

open Matrix

/-- **Theorem 3.14** (arXiv:2604.07178, version of 2026-11-03, p.25). Suppose a depth-`d`, width-`w`
2D-QAC circuit computes `f : {0,1}^n → {0,1}` exactly from product ancillas. Then
`as(f) ≤ K^d · √n · w^{3d+1/2}`. For `d ≥ 1`, this implies `w = Ω((as(f)²/n)^{1/(6d+1)})`. The
implicit constant is absolute and independent of `d`.

**Formalization Note.**
* `K` is "the same constant K" as in Theorem 3.7 (p.25), encoded by restating Theorem 3.7's bound for
  this `K` in the first conjunct.
* The `Ω` constant `c` is absolute: it is chosen before `d`.
* Inputs at any injective placement, output at any qubit, any product ancilla state;
  `w^{3d+1/2}` and the `1/(6d+1)`-th power are real powers. At `n = 0`, `as(f)²/n` is `0`. -/
theorem theorem_3_14 : ∃ K : ℝ, 2 ≤ K ∧
    (∀ (w h d : ℕ) (C : QACCircuit (Pos w h) d), C.Is2D →
      lmv (pureState (C.matrix *ᵥ basisVec (fun _ => false))) ≤ (K * (w : ℝ) ^ 3) ^ d) ∧
    (∀ (n w h d : ℕ) (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
      (anc : Pos w h → Bool → ℂ) (out : Pos w h) (f : (Fin n → Bool) → Bool),
      C.Is2D → ComputesExactly C inp anc out f →
        avgSens f ≤ K ^ d * Real.sqrt n * (w : ℝ) ^ ((3 * d : ℝ) + 1 / 2)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 1 ≤ d →
      ∀ (n w h : ℕ) (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
        (anc : Pos w h → Bool → ℂ) (out : Pos w h) (f : (Fin n → Bool) → Bool),
        C.Is2D → ComputesExactly C inp anc out f →
          c * (avgSens f ^ 2 / n) ^ ((1 : ℝ) / (6 * (d : ℝ) + 1)) ≤ w := by sorry

end GeoQAC
