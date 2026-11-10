-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_lemma_5_6
-- name    : MatMulPolyBarrier.Operational.lemma_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:29.529209+00:00
-- url     : https://prove2.me/theorems/725d7ee4-b4e3-4437-b91f-22bc2f9aadaa
-- title:
--   Lemma 5.6 — the $\theta$ with $ap_2+bp_3+cp_1=(ab+bc+ca)^2/(4abc)$ when $c(a+b)>ab$
-- statement:
--   Let $a\ge b\ge c\ge0$ be real numbers with $c(a+b)>ab$, and let
--   $$\theta_1:=1-\frac{2ab}{ab+bc+ca},\quad\theta_2:=1-\frac{2bc}{ab+bc+ca},\quad\theta_3:=1-\frac{2ac}{ab+bc+ca}.$$
--   Then $\theta=(\theta_1,\theta_2,\theta_3)\in\Theta$ and
--   $$\frac{a\theta_2}{(1-\theta_1)(1-\theta_3)}+\frac{b\theta_3}{(1-\theta_1)(1-\theta_2)}+\frac{c\theta_1}{(1-\theta_2)(1-\theta_3)}=\frac{(ab+bc+ca)^2}{4abc}.$$
--   The left side is $ap_2+bp_3+cp_1$; this choice of $\theta$ gives the second case of the barrier (5.1).
--
--   Differences from the source:
--   - encoding: θ₁, θ₂, θ₃ defined by the displayed formulas → θ : Fin 3 → ℝ with hypotheses θ 0 = …, θ 1 = …, θ 2 = … (the same formulas); reason: Lean indexing, same instance
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 39, Lemma 5.6

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- Lemma 5.6, p. 39: let `a ≥ b ≥ c ≥ 0` be reals with `c(a + b) > ab`, and
`θ₁ := 1 − 2ab/(ab + bc + ca)`, `θ₂ := 1 − 2bc/(ab + bc + ca)`, `θ₃ := 1 − 2ac/(ab + bc + ca)`.
Then `θ ∈ Θ` and
`aθ₂/((1 − θ₁)(1 − θ₃)) + bθ₃/((1 − θ₁)(1 − θ₂)) + cθ₁/((1 − θ₂)(1 − θ₃)) = (ab + bc + ca)²/(4abc)`. -/
theorem lemma_5_6 (a b c : ℝ) (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 ≤ c)
    (h : a * b < c * (a + b)) (θ : Fin 3 → ℝ)
    (hθ₁ : θ 0 = 1 - 2 * a * b / (a * b + b * c + c * a))
    (hθ₂ : θ 1 = 1 - 2 * b * c / (a * b + b * c + c * a))
    (hθ₃ : θ 2 = 1 - 2 * a * c / (a * b + b * c + c * a)) :
    InTheta θ ∧
      a * θ 1 / ((1 - θ 0) * (1 - θ 2)) + b * θ 2 / ((1 - θ 0) * (1 - θ 1)) +
          c * θ 0 / ((1 - θ 1) * (1 - θ 2)) =
        (a * b + b * c + c * a) ^ 2 / (4 * a * b * c) := by sorry

end MatMulPolyBarrier.Operational
