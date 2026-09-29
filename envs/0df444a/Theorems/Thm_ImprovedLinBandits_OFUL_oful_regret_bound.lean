-- Prove2me | Theorems.Thm_ImprovedLinBandits_OFUL_oful_regret_bound
-- name    : ImprovedLinBandits.OFUL.oful_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:22:16.566613+00:00
-- url     : https://prove2.me/theorems/e5ebb084-a747-4398-bc89-028234049d1d
-- title:
--   Theorem 3 — high-probability regret bound for OFUL
-- statement:
--   Consider the linear stochastic bandit of the paper. In round $t \ge 1$ the learner receives a decision set $D_t \subseteq \mathbb R^d$ ($d \ge 1$), picks $X_t \in D_t$ and observes $Y_t = \langle X_t, \theta_* \rangle + \eta_t$. There is a filtration $\{F_t\}$ such that $X_t$ is $F_{t-1}$-measurable and $\eta_t$ is $F_t$-measurable and conditionally $R$-sub-Gaussian given $F_{t-1}$ ($R \ge 0$). Assume
--
--   1. $\|\theta_*\|_2 \le S$ and $\|X_t\|_2 \le L$ for all $t \ge 1$;
--   2. every $D_t$ is nonempty and $\langle x, \theta_* \rangle \in [-1, 1]$ for all $t$ and all $x \in D_t$;
--   3. $\lambda \ge \max(1, L^2)$;
--   4. the actions are chosen by the OFUL algorithm, run with the confidence sets $C_t$ of Theorem 2 (with the same $R, S, \lambda, \delta$), under any tie-breaking.
--
--   Then for every $\delta > 0$, with probability at least $1 - \delta$, the pseudo-regret $R_n = \sum_{t=1}^n \langle x^*_t - X_t, \theta_*\rangle$ satisfies
--
--   $$\forall n \ge 0, \quad R_n \le 4\sqrt{nd\log(\lambda + nL^2/d)}\left(\lambda^{1/2}S + R\sqrt{2\log(1/\delta) + d\log(1 + nL^2/(\lambda d))}\right).$$
--
--   This is the $\widetilde O(d\sqrt n)$ high-probability regret bound for OFUL, uniform over the horizon.
--
--   **Formalization Note** Two corrections of the printed statement are made. (a) The paper prints $nL/d$ in both logarithms; the determinant–trace bound $\det \overline V_n \le (\lambda + nL^2/d)^d$ gives $nL^2/d$, which is stated here. For $L \le 1$ this implies the printed bound. (b) The hypothesis $\lambda \ge \max(1, L^2)$ is added: for $\lambda < 1$ the printed $\log(\lambda + nL/d)$ can be negative, Lean's square root is then $0$, and the printed bound would claim $R_n \le 0$. The optimal reward $\langle x^*_t, \theta_*\rangle$ is the supremum over $D_t$, which is finite by assumption 2. The outer probability of the failure event "there is $n$ with $R_n$ above the bound" is bounded by $\delta$. The actions' measurability is assumed, as in Theorem 1; for a run of OFUL it depends on a measurable choice of the argmax. `StandardBorelSpace` $\Omega$ is added as in Theorem 1. Nonemptiness of $D_t$ is also implied by assumption 4.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 5, Theorem 3 (with the confidence sets C_n of Theorem 2, p. 4)

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_ImprovedLinBandits_OFUL_confidenceSet
import Definitions.Def_ImprovedLinBandits_OFUL_IsOFULRun
import Definitions.Def_ImprovedLinBandits_OFUL_pseudoRegret

open MeasureTheory ProbabilityTheory Matrix NNReal

namespace ImprovedLinBandits.OFUL

/-- **Theorem 3** (The regret of the OFUL algorithm; Abbasi-Yadkori, Pál, Szepesvári, NIPS 2011,
p. 5), for OFUL run with the confidence sets `C_t` of Theorem 2 (`V = λI`), with two disclosed
corrections of the printed statement: `nL²/d` in place of the printed `nL/d` (both occurrences;
the determinant–trace bound `det V̄_n ≤ (λ + nL²/d)^d` gives `L²`), and the added hypothesis
`λ ≥ max(1, L²)` (for `λ < 1` the printed `log(λ + nL/d)` can be negative and the printed bound
fails). Under the model of Theorems 1–2 (filtration, `ℱ_t`-measurable actions, conditionally
`R`-sub-Gaussian noise, `‖θ*‖₂ ≤ S`, `‖X_t‖₂ ≤ L`), nonempty decision sets on which
`⟨x, θ*⟩ ∈ [-1, 1]`, and for any `δ > 0`, the event that for some `n ≥ 0`
`R_n > 4 √(n d log(λ + nL²/d)) (λ^{1/2} S + R √(2 log(1/δ) + d log(1 + nL²/(λd))))`
has (outer) probability at most `δ`. -/
theorem oful_regret_bound
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (D : ℕ → Ω → Set (Fin d → ℝ))
    (X : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (θtilde : ℕ → Ω → Fin d → ℝ) (θstar : Fin d → ℝ)
    (R : ℝ≥0) {S lam L δ : ℝ}
    (hd : 0 < d)
    (hX : ∀ t : ℕ, Measurable[ℱ t] (X (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) (R ^ 2) P)
    (hY : ∀ (t : ℕ) (ω : Ω), Y (t + 1) ω = X (t + 1) ω ⬝ᵥ θstar + η (t + 1) ω)
    (hS : Real.sqrt (θstar ⬝ᵥ θstar) ≤ S)
    (hL : ∀ (t : ℕ) (ω : Ω), Real.sqrt (X (t + 1) ω ⬝ᵥ X (t + 1) ω) ≤ L)
    (hlam_one : 1 ≤ lam) (hlam_L : L ^ 2 ≤ lam)
    (hD : ∀ (t : ℕ) (ω : Ω), (D (t + 1) ω).Nonempty)
    (hrew : ∀ (t : ℕ) (ω : Ω), ∀ x ∈ D (t + 1) ω, x ⬝ᵥ θstar ∈ Set.Icc (-1 : ℝ) 1)
    (hrun : IsOFULRun d R S lam δ D X Y θtilde)
    (hδ : 0 < δ) :
    P {ω | ∃ n : ℕ,
        4 * Real.sqrt ((n : ℝ) * d * Real.log (lam + (n : ℝ) * L ^ 2 / d)) *
            (Real.sqrt lam * S + (R : ℝ) * Real.sqrt (2 * Real.log (1 / δ)
              + (d : ℝ) * Real.log (1 + (n : ℝ) * L ^ 2 / (lam * d))))
          < pseudoRegret d D X θstar n ω}
      ≤ ENNReal.ofReal δ := by sorry

end ImprovedLinBandits.OFUL
