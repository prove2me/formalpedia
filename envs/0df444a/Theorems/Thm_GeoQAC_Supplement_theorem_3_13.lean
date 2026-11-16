-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_3_13
-- name    : GeoQAC.Supplement.theorem_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:22:55.331204+00:00
-- url     : https://prove2.me/theorems/8206e709-7116-404c-a9a3-3055440cf8a3
-- title:
--   Theorem 3.13 — Fourier tail bound for exact 2D-QAC functions
-- statement:
--   For every depth $d\ge1$ there is a constant $C_d>0$ such that the following holds. Let a depth-$d$ $[w,h]$-2D-QAC circuit compute $f:\{0,1\}^n\to\{0,1\}$ exactly from product ancillas, with the inputs and the output qubit at arbitrary positions. Let $h=(-1)^f$ be the sign representation of $f$ and $\mu=\mathbb E_x[h(x)]$. Then for every integer $k\ge1$
--   $$
--   W^{\ge k}[h]\le C_d\cdot\frac{n\,w^{6d+1}}{(1+\mu^2)\,k^2}.
--   $$
--
--   Functions computed exactly by narrow constant-depth 2D-QAC circuits thus have little Fourier weight on high degrees.
--
--   Differences from the source:
--   - encoding: ancillas |0^a⟩ (p.10) → any product of one-qubit unit vectors (published GeoQAC.ComputesExactly); reason: one-qubit gates in L_0 convert a product ancilla state to |0^a⟩ (p.38), so the two classes of circuits compute the same functions at the same depth and width
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.13, p.24

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_ComputesExactly
import Definitions.Def_GeoQAC_Supplement_fourierCoeff

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 3.13** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.24). "We consider
fixed `d`, so the constants in the `O` notation below may depend on `d`. If a depth-`d`, width-`w`
2D-QAC circuit computes `f : {0,1}^n → {0,1}` exactly, then, for every integer `k ≥ 1` and constant
`d ≥ 1`, `W^{≥k}[h] ≤ O(n w^{6d+1}/((1 + µ²)k²))`. Here `h(x) = (−1)^{f(x)}` is the sign
representation of `f`, and `µ = E_x[h(x)]`."

**Formalization Note.**
* `∀ d ∃ C_d`: the constant may depend on `d`, as the page says, and on nothing else (not on `n`,
  `w`, `h`, `k`, `f`, the placement or the ancillas).
* Exact computation is the published `GeoQAC.ComputesExactly`: inputs at any injective placement,
  output at any qubit, ancillas in any product of one-qubit unit vectors (the paper's default
  `|0^a⟩`, p.10, is the special case; one-qubit gates convert one into the other), garbage allowed.
* `W^{≥k}[h] = Σ_{|S| ≥ k} ĥ(S)²` with `ĥ(S) = E_x[h(x)χ_S(x)]`, `x` uniform (§2.1, p.9). -/
theorem theorem_3_13 : ∀ d : ℕ, 1 ≤ d → ∃ Cd : ℝ, 0 < Cd ∧
    ∀ (n w h : ℕ) (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
      (anc : Pos w h → Bool → ℂ) (out : Pos w h) (f : (Fin n → Bool) → Bool),
      C.Is2D → ComputesExactly C inp anc out f →
      ∀ k : ℕ, 1 ≤ k →
        fourierWeightGe (signFn f) k ≤
          Cd * n * (w : ℝ) ^ (6 * d + 1) / ((1 + signMean f ^ 2) * (k : ℝ) ^ 2) := by sorry

end GeoQAC.Supplement
