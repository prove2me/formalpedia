-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_greedy_regret_bound
-- name    : LinParamBandits.PEGE.greedy_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:38.379112+00:00
-- url     : https://prove2.me/theorems/e0a2118b-5381-41ed-b51b-4c02cc9f497d
-- title:
--   Lemma 3.6 — E[max_u z′(u − G(c)) | Z = z] ≤ r h₂/(c‖z‖)
-- statement:
--   Under Assumption 1 with constants $\sigma_0, \bar u, \lambda_0 > 0$ and the SBAR($J$) condition with $J > 0$, there is a constant $h_2 > 0$, depending only on $\sigma_0, \bar u, \lambda_0, J$, such that for every dimension $r \ge 2$, every instance satisfying these conditions, every greedy rule, every $z \in \mathbb R^r \setminus \{0\}$ and every cycle $c \ge 1$,
--   $$\mathbb E\Big[\max_{u \in \mathcal U_r} z'\big(u - G(c)\big) \,\Big|\, Z = z\Big] \le \frac{r\, h_2}{c\,\|z\|},$$
--   where $G(c)$ is the greedy arm played in the exploitation phase of cycle $c$.
--
--   The bound controls the expected instantaneous regret in every exploitation period of cycle $c$; summed over the $c$ periods of the phase it gives $r h_2/\|z\|$ per cycle.
--
--   **Formalization Note** The page says "for any $z \in \mathbb R^r$", but the right side is undefined at $z = 0$ (the proof calls that case trivially true, reading the bound as $+\infty$); the statement is made for $z \ne 0$. The greedy rule is any measurable selection of a maximizer of $v'\widehat Z(c)$; in particular it is arbitrary when $\widehat Z(c) = 0$. The constant is chosen before $r$ and the instance.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma 3.6, p. 17

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Lemma 3.6 (Regret Under the Greedy Decision), Rusmevichientong, Tsitsiklis,
arXiv:0812.3465v2, p. 17: under Assumption 1 and SBAR(`J`) there is a positive constant `h₂`,
depending only on `σ₀, ū, λ₀, J`, such that for any `z ∈ ℝ^r \ {0}` and `c ≥ 1`,
`E[max_{u ∈ 𝒰_r} z′(u − G(c)) | Z = z] ≤ r h₂ / (c ‖z‖)`, where `G(c) = g c (Ẑ(c))` is the greedy
arm of cycle `c`, ties broken by any measurable rule `g`. The page says "for any `z ∈ ℝ^r`"; the
bound is stated for `z ≠ 0`, where its right side is defined. -/
theorem greedy_regret_bound (σ₀ ū lam₀ J : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (hJ : 0 < J) :
    ∃ h₂ : ℝ, 0 < h₂ ∧
      ∀ (r : ℕ), 2 ≤ r →
      ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
        (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r),
      Assumption1 𝒰 ν b σ₀ ū lam₀ → SBAR 𝒰 J → GreedySelector 𝒰 g →
      ∀ (z : LinParamBandits.LowerBound.Vec r), z ≠ 0 → ∀ (c : ℕ), 1 ≤ c →
        ∫⁻ w, ENNReal.ofReal (LinParamBandits.UEGeneral.bestValue 𝒰 z - inner ℝ (g c (Zhat b z w c)) z) ∂(noiseLaw ν b)
          ≤ ENNReal.ofReal (r * h₂ / (c * ‖z‖)) := by sorry
end LinParamBandits.PEGE
