-- Prove2me | Theorems.Thm_LargeBSP_Homog_eq_A4
-- name    : LargeBSP.Homog.eq_A4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:59.307738+00:00
-- url     : https://prove2.me/theorems/165d0dff-717e-409b-9905-2f657b33ee48
-- title:
--   (A4), pp. A1–A2 — P(V_N(⌊Nt⋆⌋) > N V̄(t⋆) − g(N)) → 1
-- statement:
--   Let $X_1, X_2, \dots$ be measurable valuations on a probability space, $\bar V : \mathbb R \to \mathbb R$, $t^\star \in \mathbb R$, and let $g(N)$ be eventually positive with
--   $$\frac{\mathbb E\big[(V_N(\lfloor N t^\star \rfloor) - N \bar V(t^\star))^2\big]}{g(N)^2} \to 0,$$
--   i.e. $g(N) \in \omega_+\big(\sqrt{\mathbb E[(V_N(\lfloor Nt^\star\rfloor) - N\bar V(t^\star))^2]}\big)$. Then
--   $$\mathbb P\big(V_N(\lfloor N t^\star \rfloor) > N \bar V(t^\star) - g(N)\big) \to 1 \qquad (N \to \infty).$$
--
--   In the proof of Theorem 1 this is the probability that the customer buys the single offered size $\lfloor Nt^\star \rfloor$ at price $N\bar V(t^\star) - g(N)$.
--
--   **Formalization Note** The second moment is a lower Lebesgue integral in $[0,\infty]$, so it may be infinite; the hypothesis then fails, as it should. For $g > 0$, $g/\sqrt m \to \infty$ is equivalent to $m/g^2 \to 0$ (also when $m = 0$), which is the form used. Measurability of the valuations is the paper's "random vector".
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 1 (Appendix A.1), pp. A1–A2, (A4)

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- (A4), pp. A1–A2: if `g(N) ∈ ω₊(√E[(V_N(⌊Nt⋆⌋) − N V̄(t⋆))²])`, then
`P(V_N(⌊Nt⋆⌋) > N V̄(t⋆) − g(N)) → 1`. -/
theorem eq_A4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (Vl : ℝ → ℝ) (t₀ : ℝ)
    (g : ℕ → ℝ) (hg0 : ∀ᶠ N in atTop, 0 < g N)
    (hgω : Tendsto (fun N : ℕ =>
      (∫⁻ ω, ENNReal.ofReal ((V (fun n => X n ω) N ⌊(N : ℝ) * t₀⌋₊ - N * Vl t₀) ^ 2) ∂P) /
        ENNReal.ofReal (g N ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (P {ω | (N : ℝ) * Vl t₀ - g N < V (fun n => X n ω) N ⌊(N : ℝ) * t₀⌋₊}).toReal)
      atTop (𝓝 1) := by sorry

end LargeBSP.Homog
