-- Prove2me | Theorems.Thm_GenEmpLik_Expansion_lemma_1
-- name    : GenEmpLik.Expansion.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:25:17.728173+00:00
-- url     : https://prove2.me/theorems/d30a4b25-4456-49d8-a2fd-83b86758596d
-- title:
--   Lemma 1 — the f-divergence robust mean equals $E_{\widehat P_n}[Z]+\sqrt{\rho s_n^2/n}+o(n^{-1/2})$ almost surely
-- statement:
--   Let $Z_1,Z_2,\dots$ be a strictly stationary ergodic sequence of real random variables with $E[Z_1^2]<\infty$, and let $f$ satisfy Assumption A. Fix $\rho\ge0$. For each $n$ let $\widehat P_n$ be the empirical distribution of $Z_1,\dots,Z_n$ and $s_n^2=E_{\widehat P_n}[Z^2]-E_{\widehat P_n}[Z]^2$ the sample variance. Then
--
--   $$
--   \Big|\sup_{P:\,D_f(P\|\widehat P_n)\le\rho/n}E_P[Z]-E_{\widehat P_n}[Z]-\sqrt{\frac\rho n s_n^2}\Big|\le\frac{\epsilon_n}{\sqrt n}
--   \qquad\text{with}\qquad \epsilon_n\xrightarrow{\text{a.s.}}0 .
--   $$
--
--   Equivalently, almost surely
--
--   $$
--   \sqrt n\,\Big|\sup_{P:\,D_f(P\|\widehat P_n)\le\rho/n}E_P[Z]-E_{\widehat P_n}[Z]-\sqrt{\frac\rho n s_n^2}\Big|\longrightarrow0\qquad(n\to\infty).
--   $$
--
--   The robust mean is therefore the sample mean plus a variance penalty, up to an error of smaller order than $n^{-1/2}$. Combined with the central limit theorem this gives the asymptotically exact $\chi^2_1$ coverage of generalized empirical likelihood intervals for a mean.
--
--   **Formalization Note** The supremum is over $P\ll\widehat P_n$ (`robustMean`); mean and variance are the published `empMean` and `empVar`. Stationarity and ergodicity is `IsStationaryErgodic` (the law of the path is invariant and ergodic for the shift). The paper's $\epsilon_n\to0$ a.s. is stated as the almost sure convergence of $\sqrt n$ times the left-hand side, which is the same statement (take $\epsilon_n$ equal to that quantity). Lean's `Z 0` is the paper's $Z_1$, and the first $n$ observations are `Z 0, …, Z (n-1)`.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 7, Lemma 1, (8)

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_AssumptionA
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_GenEmpLik_Expansion_IsStationaryErgodic
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar

open MeasureTheory ProbabilityTheory Filter Topology VarianceRegularization.Expansion

namespace GenEmpLik.Expansion

/-- Lemma 1 (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 7, (8)). Let `Z 0, Z 1, …` (the
paper's `Z₁, Z₂, …`) be a strictly stationary ergodic sequence of real random variables with
`E[Z₁²] < ∞`, and let Assumption A hold. With `P̂_n` the empirical distribution of the first `n`
observations and `s_n² = E_{P̂n}[Z²] − E_{P̂n}[Z]²`,
`| sup_{P : D_f(P‖P̂n) ≤ ρ/n} E_P[Z] − E_{P̂n}[Z] − √(ρ/n · s_n²) | ≤ ε_n / √n` with `ε_n → 0`
almost surely; equivalently, `√n` times the left-hand side tends to `0` almost surely. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (f : ℝ → EReal) (hA : AssumptionA f) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (Z : ℕ → Ω → ℝ) (hZ : IsStationaryErgodic Z P)
    (hmom : Integrable (fun ω => Z 0 ω ^ 2) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.sqrt n *
      |robustMean f ρ (fun i : Fin n => Z i ω) - empMean (fun i : Fin n => Z i ω) -
        Real.sqrt (ρ / n * empVar (fun i : Fin n => Z i ω))|) atTop (𝓝 0) := by sorry

end GenEmpLik.Expansion
