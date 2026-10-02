-- Prove2me | Theorems.Thm_MDPFinance_TerminalWealth_one_period_optimal_existence
-- name    : MDPFinance.TerminalWealth.one_period_optimal_existence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:54:02.553022+00:00
-- url     : https://prove2.me/theorems/fdaa1b65-c565-40cd-8ed7-5e18cbbe36f2
-- title:
--   Theorem 4.1.1 — one-period no-arbitrage iff existence of an optimal portfolio
-- statement:
--   Let $U$ be a utility function with $\mathrm{dom}\,U = [0,\infty)$ or $(0,\infty)$. Then: a) there
--   is no arbitrage iff there is a measurable $f^*: \mathrm{dom}\,U \to \mathbb{R}^d$ with
--   $u(x,f^*(x)) = v(x)$ for all $x$; b) $v$ is strictly increasing, strictly concave and continuous.
--
--   **Formalization Note.** The domain restriction (`[0,\infty)` or `(0,\infty)`) is a genuine
--   hypothesis, not a simplifying choice: Remark 4.1.2 (not separately formalized as its own item,
--   since it carries no number) notes the result extends to $\mathrm{dom}\,U = \mathbb{R}$ *bounded
--   above* but fails for $\mathrm{dom}\,U=\mathbb{R}$ unbounded above — the exponential-utility case
--   (Theorem 4.2.15) relies on this extension, cited explicitly rather than silently reused.
--
--   **Formalization Note (moderation).** The one-period market has a positive bond factor
--   $1+i>0$ and, as Section 4.1 assumes, $\mathbb{E}\|R\|<\infty$; $u$, $v$ are
--   $[-\infty,\infty)$-valued and $v$'s strict concavity is `StrictConcaveOnEReal`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 77, PDF 91, Theorem 4.1.1

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_OnePeriod

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.1.1 (Bäuerle–Rieder, p. 77, PDF 91). In the one-period market of Section 4.1
(bond factor `1 + i > 0`, relative risk `R` with `𝔼‖R‖ < ∞`, the section's integrability
assumption), let `U` be a utility function with `domU = [0,∞)` or `domU = (0,∞)`. Then: a) there
are no arbitrage opportunities if and only if there exists a measurable `f* : domU → ℝ^d` such
that `u(x,f*(x)) = v(x)` for all `x ∈ domU`; b) `v` is strictly increasing, strictly concave and
continuous on `domU`. -/
theorem one_period_optimal_existence {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (measIP : Measure Ω) [IsProbabilityMeasure measIP] (domU : Set ℝ)
    (hdomU : domU = Set.Ici (0 : ℝ) ∨ domU = Set.Ioi (0 : ℝ)) (U : ℝ → ℝ)
    (hU : StrictMonoOn U domU ∧ StrictConcaveOn ℝ domU U ∧ ContinuousOn U domU)
    (i : ℝ) (hi : 0 < 1 + i) (R : Ω → Fin d → ℝ) (hR_meas : Measurable R)
    (hR_integrable : Integrable (fun ω => ∑ k, |R ω k|) measIP) :
    (NoArbitrageOnePeriod measIP R ↔
      ∃ fstar : ℝ → (Fin d → ℝ), Measurable fstar ∧
        ∀ x ∈ domU, OnePeriodU measIP U i R x (fstar x) = OnePeriodV measIP domU U i R x) ∧
      StrictMonoOn (OnePeriodV measIP domU U i R) domU ∧
      StrictConcaveOnEReal domU (OnePeriodV measIP domU U i R) ∧
      ContinuousOn (OnePeriodV measIP domU U i R) domU := by sorry

end MDPFinance.TerminalWealth
