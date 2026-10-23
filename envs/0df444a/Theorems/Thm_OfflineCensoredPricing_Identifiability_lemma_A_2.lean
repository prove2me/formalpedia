-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_A_2
-- name    : OfflineCensoredPricing.Identifiability.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:55.716131+00:00
-- url     : https://prove2.me/theorems/e5aa192c-80c8-472d-a08b-6fa812e804ce
-- title:
--   Lemma A.2, p. 35 — Dvoretzky–Kiefer–Wolfowitz inequality (Massart): P[sup_x |F̂ₙ(x) − F(x)| ≤ ε] ≥ 1 − 2e^{−2nε²}, any c.d.f.
-- statement:
--   Let $\mu$ be any probability measure on $\mathbb R$ with c.d.f. $F$, let $X_1, \dots, X_n$ be i.i.d. with law $\mu$, and let $\hat F_n(x) = \frac1n\#\{j : X_j \le x\}$ be their empirical distribution function. Then for any $\varepsilon > 0$,
--   $$\mathbb P\Big[\sup_{x\in\mathbb R} |\hat F_n(x) - F(x)| \le \varepsilon\Big] \ge 1 - 2e^{-2n\varepsilon^2}.$$
--
--   This is the Dvoretzky–Kiefer–Wolfowitz inequality with Massart's tight constant. In the paper it controls the empirical c.d.f. of the censored sales $\min\{\xi - bp_i, y_i\}$ in the proof of Lemma 1 ((D.1), p. 42).
--
--   **Formalization Note** No continuity of $F$ is assumed: the censored sales have an atom at $y_i$. The statement bounds the outer probability of the failure event $\{\exists x,\ |\hat F_n(x) - F(x)| > \varepsilon\}$ by $2e^{-2n\varepsilon^2}$. For $n = 0$ the bound is $2$ (with $0/0 = 0$ in Lean) and holds trivially.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 35, Lemma A.2 (citing Massart 1990)

import Mathlib

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory ProbabilityTheory

/-- **Lemma A.2** (Dvoretzky–Kiefer–Wolfowitz inequality, Massart 1990; p. 35). Let `F̂ₙ` be the
empirical distribution function of `n` i.i.d. samples of a random variable with c.d.f. `F`. Then for
any `ε > 0`, `P[sup_{x ∈ ℝ} |F̂ₙ(x) − F(x)| ≤ ε] ≥ 1 − 2e^{−2nε²}`. Stated for an arbitrary probability
measure `μ` on `ℝ` (no continuity of `F`), as an upper bound on the outer probability of the failure
event `∃ x, |F̂ₙ(x) − F(x)| > ε`. -/
theorem lemma_A_2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Measure.pi (fun _ : Fin n => μ)
        {ω | ∃ x : ℝ,
          ε < |((Finset.univ.filter (fun j => ω j ≤ x)).card : ℝ) / (n : ℝ) - cdf μ x|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * (n : ℝ) * ε ^ 2))) := by sorry

end OfflineCensoredPricing.Identifiability
