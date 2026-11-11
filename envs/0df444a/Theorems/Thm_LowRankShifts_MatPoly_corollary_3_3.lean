-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_corollary_3_3
-- name    : LowRankShifts.MatPoly.corollary_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:56:41.652219+00:00
-- url     : https://prove2.me/theorems/6168c94c-9c16-4805-aa2c-46443f6b4548
-- title:
--   Corollary 3.3 — an algorithm correct on an α fraction is correct with probability ≥ α/2 on random low-rank shifts of almost every input
-- statement:
--   Let $p$ be a prime, $D$ a (possibly randomized) algorithm on $\mathbb F_p^{n\times m}$ — for each input $X$ a law $D(X)$ on outputs — and $g$ a function on $\mathbb F_p^{n\times m}$ with values in the same output set. Let $\alpha=\Pr_{X\sim\mathbb F_p^{n\times m}}[D(X)=g(X)]$, over uniform $X$ and $D$'s randomness. Then
--
--   $$\Pr_{A\sim\mathbb F_p^{n\times m}}\Big[\Pr_{U\sim\mathbb F_p^{n\times r},\,V\sim\mathbb F_p^{m\times r}}\big[D(A+UV^T)=g(A+UV^T)\big]\ge\frac\alpha2\Big]\ \ge\ 1-\frac{4p^{-2r}}{\alpha},$$
--
--   and if $\alpha\ge 1/2+\varepsilon$ for some $\varepsilon>0$, the same with $1/2+\varepsilon/2$ in place of $\alpha/2$ and $1-4p^{-2r}/\varepsilon^2$ on the right.
--
--   Theorem 3.5 applies it with $m=\ell n$ to an oracle for a matrix polynomial: for almost every input, a random low-rank shift of it is answered correctly with probability at least $\alpha/2$.
--
--   **Formalization Note.** $D$ is a map to `PMF β` for an arbitrary output type $\beta$; inner probabilities include $D$'s randomness.
--
--   Differences from the source:
--   - encoding: a (possibly randomized) algorithm D : F_p^{n×m} → R and a function g : F_p^{n×m} → R, R an arbitrary output set (italic R on the page, not ℝ) → `D : Matrix … → PMF β` (the law of D's output on each input) and `g : Matrix … → β` for an arbitrary type β; reason: the same objects; a randomized algorithm is described by the law of its output
--   - encoding: Pr_{A∼F_p^{n×m}}[·] and E_{U∼F_p^{n×r}, V∼F_p^{m×r}}[·] → `unifProb` over A and `unifMean` over pairs (U, V); reason: uniform probabilities and expectations on finite sets
--   - encoding: 4p^{−2r}/α at α = 0 (undefined) → Lean's division by zero gives 0, so the first claim at α = 0 is probability ≥ 1; reason: true at α = 0, since every probability is ≥ 0 = α/2; no instance is added or removed
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 18 (PDF 21), Corollary 3.3

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform

open Matrix

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-- Corollary 3.3 (p. 18): for any prime `p`, any (possibly randomized) algorithm
`D : F_p^{n×m} → β` (a law `D X` on outputs for each input) and any `g : F_p^{n×m} → β`, with
`α := Pr_X[D(X) = g(X)]`,
`Pr_A[Pr_{U,V}[D(A + UVᵀ) = g(A + UVᵀ)] ≥ α/2] ≥ 1 − 4p^{−2r}/α`; and if `α ≥ 1/2 + ε` with
`ε > 0`, `Pr_A[Pr_{U,V}[D(A + UVᵀ) = g(A + UVᵀ)] ≥ 1/2 + ε/2] ≥ 1 − 4p^{−2r}/ε²`. -/
theorem corollary_3_3 {p : ℕ} [Fact p.Prime] (n m r : ℕ) {β : Type*}
    (D : Matrix (Fin n) (Fin m) (ZMod p) → PMF β) (g : Matrix (Fin n) (Fin m) (ZMod p) → β) :
    let α : ℝ := ZamirInversion581.Mult.unifMean fun X => (D X (g X)).toReal
    let q : Matrix (Fin n) (Fin m) (ZMod p) → ℝ := fun A =>
      ZamirInversion581.Mult.unifMean
        fun UV : Matrix (Fin n) (Fin r) (ZMod p) × Matrix (Fin m) (Fin r) (ZMod p) =>
          (D (A + UV.1 * UV.2ᵀ) (g (A + UV.1 * UV.2ᵀ))).toReal
    (1 - 4 * ((p : ℝ) ^ (2 * r))⁻¹ / α ≤
        ZamirInversion581.Mult.unifProb fun A => α / 2 ≤ q A) ∧
    (∀ ε : ℝ, 0 < ε → 1 / 2 + ε ≤ α →
      1 - 4 * ((p : ℝ) ^ (2 * r))⁻¹ / ε ^ 2 ≤
        ZamirInversion581.Mult.unifProb fun A => 1 / 2 + ε / 2 ≤ q A) := by sorry

end LowRankShifts.MatPoly
