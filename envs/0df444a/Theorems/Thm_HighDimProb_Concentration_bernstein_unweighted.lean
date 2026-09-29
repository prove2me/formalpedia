-- Prove2me | Theorems.Thm_HighDimProb_Concentration_bernstein_unweighted
-- name    : HighDimProb.Concentration.bernstein_unweighted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:37:30.147061+00:00
-- url     : https://prove2.me/theorems/ffb81651-cac7-4739-85c2-9cb4b69885be
-- title:
--   Theorem 2.8.1 — Bernstein's inequality
-- statement:
--   This is **Bernstein's inequality** for an unweighted sum of independent, mean-zero,
--   sub-exponential random variables — the direct predecessor of the goal theorem of this
--   mission, with all weights $a_i = 1$.
--
--   There exists an absolute constant $c > 0$ (not depending on the sample size, the random
--   variables, or the deviation level) such that the following holds. Let
--   $(\Omega, \mathcal F, P)$ be a probability space, let $N \in \mathbb N$, and let
--   $X_1, \dots, X_N : \Omega \to \mathbb R$ be independent, mean-zero, sub-exponential random
--   variables (finite $\|X_i\|_{\psi_1}$). Then, for every $t \ge 0$,
--
--   $$
--   P\Bigl\{\Bigl|\sum_{i=1}^N X_i\Bigr| \ge t\Bigr\}
--     \;\le\; 2\exp\!\left[-c\min\!\left(\frac{t^2}{\sum_i \|X_i\|_{\psi_1}^2},
--       \frac{t}{\max_i \|X_i\|_{\psi_1}}\right)\right].
--   $$
--
--   The bound has two regimes: a sub-gaussian tail near the mean (as the central limit
--   theorem would suggest) transitioning, in the far tail, to a heavier sub-exponential decay
--   driven by whichever single term $X_i$ has the largest sub-exponential norm. Neither term
--   of the minimum can be dropped: the sub-exponential term reflects genuinely heavier-than-
--   Gaussian tails that a purely Gaussian bound would understate, while dropping the
--   sub-gaussian term would needlessly weaken the bound near the mean, where the central-limit
--   heuristic is in fact accurate.
--
--   **Formalization Note** The sub-exponential hypothesis on each $X_i$ is stated directly, in
--   the same convention as the `subexponentialNorm` definition: $\exists\, s > 0$ with
--   $\mathbb E\exp(|X_i|/s) \le 2$. The absolute constant $c$ is existentially quantified
--   ahead of every other object, exactly as in `general_hoeffding`. $\max_i \|X_i\|_{\psi_1}$
--   is Mathlib's `iSup` over `Fin N`.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 2.8.1, p. 37 (PDF p. 45)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubexponentialNorm

open MeasureTheory ProbabilityTheory Real

namespace HighDimProb.Concentration

/-- **Theorem 2.8.1** (Bernstein's inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 37.

Let `X₁, …, X_N` be independent, mean zero, sub-exponential random variables. Then, for
every `t ≥ 0`,

`P {|∑ᵢ Xᵢ| ≥ t} ≤ 2 exp[−c min(t² / ∑ᵢ‖Xᵢ‖²_{ψ₁}, t / maxᵢ‖Xᵢ‖_{ψ₁})]`, where `c > 0` is an
absolute constant (not depending on `N`, the `Xᵢ`, or `t`). -/
theorem bernstein_unweighted :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {N : ℕ} (X : Fin N → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X P →
        (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, ∃ s > 0, Integrable (fun ω => Real.exp (|X i ω| / s)) P ∧
                       ∫ ω, Real.exp (|X i ω| / s) ∂P ≤ 2) →
        ∀ {t : ℝ}, 0 ≤ t →
        P.real {ω | t ≤ |∑ i, X i ω|} ≤
          2 * Real.exp (-(c * min
            (t ^ 2 / ∑ i, (subexponentialNorm P (X i)) ^ 2)
            (t / ⨆ i, subexponentialNorm P (X i)))) := by sorry

end HighDimProb.Concentration
