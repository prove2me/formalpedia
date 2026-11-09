-- Prove2me | Theorems.Thm_KSPolySign_lemma_6_3
-- name    : KSPolySign.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:40:47.471674+00:00
-- url     : https://prove2.me/theorems/479ba8ce-34c5-4e62-960f-24d69c52aa4f
-- title:
--   Lemma 6.3 — nonvanishing gradient or negative curvature
-- statement:
--   There is an absolute constant $\kappa_1>0$ with the following property. Let $y$ be a light state on a nonempty retained face of the algorithm: $1\le k\le n^2$ active coordinates, positive semidefinite rank-one $C_i$ with $\sum_iC_i^2\preceq I$ and $a\,n^{-2}\le\mathrm{tr}[C_i]\le1$, regularization $\rho=10^{-8}/n$, $1-|y_i|\ge\delta_{\mathrm{end}}\ge a/n$, and
--   $$P(y)\le P_0+e_{\mathrm{end}} = 2\sqrt{\iota+2\cdot10^{-8}}+10^{-6}.$$
--   Then
--   $$\|\nabla P(y)\|_\infty\ge\kappa_1n^{-12}\qquad\text{or}\qquad\lambda_{\min}\big(\nabla^2P(y)\big)\le-\kappa_1n^{-12}.$$
--
--   This quantitative form of Lemma 2.7 gives the algorithm a descent direction with a polynomially bounded certificate at every light state.
--
--   **Formalization Note** The hypotheses of Lemma 6.2 are made explicit from Lemmas 6.1 and 4.4. The constant $a>0$ of Lemma 6.1 is arbitrary and $\kappa_1$ depends only on it. All coordinates are active, so the gradient and Hessian are over all coordinates. $\lambda_{\min}\le-c$ is written as the existence of $r\ne0$ with $r^\top\nabla^2P\,r\le-c\|r\|^2$.
--
--   Differences from the source:
--   - reading: under the hypotheses of Lemma 6.2 (light state on a nonempty retained face from Lemma 6.1, 1 − |y_i| ≥ δ_end, P(y) ≤ P₀ + e_end) → explicit: 1 ≤ k ≤ n², IsInstance C, a n⁻² ≤ tr C_i ≤ 1, ρ = 10⁻⁸/n, 1 − |y_i| ≥ a/n, IsLight, P(y) ≤ 2√(ι + 2·10⁻⁸) + 10⁻⁶ (P₀ = 2√(ι + 2ε_scale), Lemma 6.1(b), p.54); reason: these are the conditions Lemmas 6.1(a–c), 4.4 and 6.2 state for that face
--   - generalization: an absolute constant a > 0 fixed by Lemma 6.1 → every a > 0, with κ₁ depending only on a; reason: the source's a is one such value
--   - generalization: the fixed contribution F produced by the algorithm → any Hermitian F; reason: the algorithm's F is Hermitian; the proof uses only the bound on P(y)
--   - generalization: 1 − |y_i| ≥ δ_end with δ_end ≥ a/n → 1 − |y_i| ≥ a/n; reason: a weaker hypothesis; every state of the source satisfies it
--   - encoding: ‖∇P(y)‖_∞ ≥ c or λ_min(∇²P(y)) ≤ −c → some |∂_iP(y)| ≥ c, or some r ≠ 0 with rᵀ∇²P(y)r ≤ −c‖r‖²; reason: equivalent definitions (the Hessian is symmetric by Lemma 3.7(c))
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 6.3, p.59 (PDF p.59); hypotheses of Lemma 6.2, p.55 (PDF p.55), from Lemma 6.1, p.54 and Lemma 4.4

import Mathlib
import Definitions.Def_KSPolySign_IsLight
import Definitions.Def_KSPolySign_IsInstance
import Definitions.Def_KSPolySign_grad
import Definitions.Def_KSPolySign_hess
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 6.3 (Nonvanishing gradient or negative curvature).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 6.3, p.59 (PDF p.59), under
the hypotheses of Lemma 6.2, p.55 (PDF p.55).

There is an absolute constant `κ₁ > 0` such that, at a light state on a nonempty retained face from
Lemma 6.1 with `1 − |y_i| ≥ δ_end` and `P(y) ≤ P₀ + e_end`, `‖∇P(y)‖_∞ ≥ κ₁n⁻¹²` or
`λ_min(∇²P(y)) ≤ −κ₁n⁻¹²`.

**Formalization Note** The hypotheses of Lemma 6.2 are made explicit from Lemmas 6.1 and 4.4:
`1 ≤ k ≤ n²` coordinates; PSD rank-one `C_i` with `∑ C_i² ⪯ I` and `an⁻² ≤ tr C_i ≤ 1`; `ρ = ε_scale/n`
with `ε_scale = 10⁻⁸`; `1 − |y_i| ≥ a/n` (Lemma 6.1(c): `δ_end ≥ a/n`); `P₀ = 2√(ι + 2ε_scale) = 2√(ι + 2·10⁻⁸)`,
`e_end = 10⁻⁶`. The absolute constant `a > 0` of Lemma 6.1 is arbitrary here (`∀ a, ∃ κ₁`), and the
fixed part `F` is any Hermitian matrix. All coordinates are active, so `∇P`, `∇²P` are `grad`, `hess`
over all of `Fin k`; `λ_min(∇²P) ≤ −c` is written as the existence of `r ≠ 0` with
`rᵀ∇²P r ≤ −c‖r‖²`. -/
theorem lemma_6_3 :
    ∀ a : ℝ, 0 < a → ∃ κ₁ : ℝ, 0 < κ₁ ∧
      ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → k ≤ n ^ 2 → ∀ C : Fin k → Matrix (Fin n) (Fin n) ℂ, IsInstance C →
        (∀ i, a / (n : ℝ) ^ 2 ≤ (C i).trace.re ∧ (C i).trace.re ≤ 1) →
        ∀ F : Matrix (Fin n) (Fin n) ℂ, F.IsHermitian → ∀ y : Fin k → ℝ, (∀ i, a / (n : ℝ) ≤ 1 - |y i|) →
        IsLight C F ((1 : ℝ) / 10 ^ 8 / n) y →
        pot C F ((1 : ℝ) / 10 ^ 8 / n) y ≤ 2 * Real.sqrt (iota + 2 / 10 ^ 8) + 1 / 10 ^ 6 →
        (∃ i, κ₁ * (n : ℝ) ^ (-12 : ℤ) ≤ |grad C F ((1 : ℝ) / 10 ^ 8 / n) y i|) ∨
          ∃ r : Fin k → ℝ, r ≠ 0 ∧
            ∑ i, ∑ j, r i * hess C F ((1 : ℝ) / 10 ^ 8 / n) y i j * r j ≤
              -(κ₁ * (n : ℝ) ^ (-12 : ℤ)) * ∑ i, r i ^ 2 := by sorry

end KSPolySign
