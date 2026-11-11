-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_lemma_3_2
-- name    : LowRankShifts.MatPoly.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:56:39.35528+00:00
-- url     : https://prove2.me/theorems/6f2df1d0-1aae-4b1d-b827-6ee89b02a7b8
-- title:
--   Lemma 3.2 — random low-rank shifts concentrate the average of any function (items 1 and 2 included)
-- statement:
--   Let $p$ be a prime, $f:\mathbb F_p^{n\times m}\to\mathbb R$, $\alpha=\mathbb E_X[f(X)]$ and $\beta=\mathbb E_X[f(X)^2]$ for uniform $X$, and
--   $$q(A)=\mathbb E_{U\sim\mathbb F_p^{n\times r},\,V\sim\mathbb F_p^{m\times r}}\big[f(A+UV^T)\big].$$
--   Then for every $\delta>0$
--
--   $$\Pr_{A\sim\mathbb F_p^{n\times m}}\big[q(A)\ge\alpha-\delta\big]\ \ge\ 1-\frac{p^{-2r}\beta}{\delta^2}.$$
--
--   In particular: (1) if $f(X)\in[0,1]$ for all $X$, then $\Pr_A[q(A)\ge\alpha/2]\ge 1-4p^{-2r}/\alpha$; (2) if $f(X)\in[0,1]$ for all $X$ and $\alpha\ge 1/2+\varepsilon$ for some $\varepsilon>0$, then $\Pr_A[q(A)\ge 1/2+\varepsilon/2]\ge 1-4p^{-2r}/\varepsilon^2$.
--
--   This is the paper's low-rank shift lemma: after a random rank-$r$ shift, almost every input sees nearly the average behaviour of $f$.
--
--   **Formalization Note.** All three parts are one statement. At $\alpha=0$ the bound $4p^{-2r}/\alpha$ of item 1 is undefined on paper; Lean's $x/0=0$ reads it as the claim that the probability is at least $1$, which holds since $f\equiv 0$ then.
--
--   Differences from the source:
--   - encoding: Pr_{A∼F_p^{n×m}}[·] and E_{U∼F_p^{n×r}, V∼F_p^{m×r}}[·] → `unifProb` over A and `unifMean` over pairs (U, V); reason: uniform probabilities and expectations on finite sets
--   - encoding: 4p^{−2r}/α at α = 0 (undefined) → Lean's division by zero gives 0, so item 1 at α = 0 claims probability ≥ 1; reason: true at α = 0 (then f ≡ 0); no instance is added or removed
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), pp. 16–17 (PDF 19–20), Lemma 3.2

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform

open Matrix

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-- Lemma 3.2 (pp. 16–17): for any prime `p`, any `f : F_p^{n×m} → ℝ` and any `δ > 0`,
`Pr_A[E_{U,V}[f(A + UVᵀ)] ≥ α − δ] ≥ 1 − p^{−2r}β/δ²` with `α := E f`, `β := E f²`; and, if
`f ∈ [0, 1]`, (1) `Pr_A[E_{U,V}[f(A + UVᵀ)] ≥ α/2] ≥ 1 − 4p^{−2r}/α`, (2) if moreover
`α ≥ 1/2 + ε` with `ε > 0`, `Pr_A[E_{U,V}[f(A + UVᵀ)] ≥ 1/2 + ε/2] ≥ 1 − 4p^{−2r}/ε²`. All of
`A ∼ F_p^{n×m}`, `U ∼ F_p^{n×r}`, `V ∼ F_p^{m×r}` are uniform and independent. -/
theorem lemma_3_2 {p : ℕ} [Fact p.Prime] (n m r : ℕ)
    (f : Matrix (Fin n) (Fin m) (ZMod p) → ℝ) :
    let α : ℝ := ZamirInversion581.Mult.unifMean f
    let β : ℝ := ZamirInversion581.Mult.unifMean fun X => f X ^ 2
    let q : Matrix (Fin n) (Fin m) (ZMod p) → ℝ := fun A =>
      ZamirInversion581.Mult.unifMean
        fun UV : Matrix (Fin n) (Fin r) (ZMod p) × Matrix (Fin m) (Fin r) (ZMod p) =>
          f (A + UV.1 * UV.2ᵀ)
    (∀ δ : ℝ, 0 < δ →
      1 - ((p : ℝ) ^ (2 * r))⁻¹ * β / δ ^ 2 ≤
        ZamirInversion581.Mult.unifProb fun A => α - δ ≤ q A) ∧
    ((∀ X, f X ∈ Set.Icc (0 : ℝ) 1) →
      1 - 4 * ((p : ℝ) ^ (2 * r))⁻¹ / α ≤
        ZamirInversion581.Mult.unifProb fun A => α / 2 ≤ q A) ∧
    ((∀ X, f X ∈ Set.Icc (0 : ℝ) 1) → ∀ ε : ℝ, 0 < ε → 1 / 2 + ε ≤ α →
      1 - 4 * ((p : ℝ) ^ (2 * r))⁻¹ / ε ^ 2 ≤
        ZamirInversion581.Mult.unifProb fun A => 1 / 2 + ε / 2 ≤ q A) := by sorry

end LowRankShifts.MatPoly
