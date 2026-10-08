-- Prove2me | Theorems.Thm_FreedmanTail_Bernstein_proposition_3_3
-- name    : FreedmanTail.Bernstein.proposition_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:54:19.769369+00:00
-- url     : https://prove2.me/theorems/b5383ace-60ba-41d5-8d14-f34ebaa300aa
-- title:
--   (3.3) Proposition — ∫_{σ<∞} Q_λ(T_σ, S_σ) dP ≤ 1 for λ ≥ 0 and any stopping time σ, under (3.4)
-- statement:
--   Let $(\Omega,\mathcal F,P)$, the filtration $(\mathcal F_n)_{n\ge0}$, the increments $X_n$ (with $X_n$ $\mathcal F_n$-measurable and square integrable), $S_n$, $T_n$ and $Q_\lambda$ be as in Definition (1.2), and assume (3.4): $X_n\le1$ a.e. and $E\{X_n\mid\mathcal F_{n-1}\}\le0$ a.e. for all $n\ge1$; no lower bound is assumed on $X_n$. Let $\sigma$ be a stopping time, taking values in $\{0,1,2,\dots,\infty\}$ with $\{\sigma\le n\}\in\mathcal F_n$ for every $n$, where $P\{\sigma=\infty\}>0$ is allowed. Then for every $\lambda\ge0$,
--   $$\int_{\{\sigma<\infty\}}Q_\lambda(T_\sigma,S_\sigma)\,dP\le1 .$$
--
--   The stopping time need not be bounded; the integral runs only over the event that it is finite. This optional-stopping bound is what turns the supermartingale into a tail estimate.
--
--   **Formalization Note** The integral is the Lebesgue integral of the nonnegative function $\omega\mapsto Q_\lambda(T_{\sigma(\omega)}(\omega),S_{\sigma(\omega)}(\omega))$ over $\{\sigma<\infty\}$, valued in $[0,\infty]$, so the bound does not presuppose integrability. Stopping times take values in `WithTop ℕ`, with $\top$ playing the role of $\infty$; $S_\sigma$, $T_\sigma$ are read through Mathlib's `stoppedValue`, and only on $\{\sigma\ne\infty\}$. Square integrability of the $X_n$ is assumed for the reason given in Definition (1.2).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 106 (PDF p. 7), (3.3) Proposition with condition (3.4)

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

/-- Freedman (1975), (3.3) Proposition, p. 106: under (3.4), for `λ ≥ 0` and any stopping
time `σ` (the value `∞ = ⊤` allowed), `∫_{σ<∞} Q_λ(T_σ, S_σ) dP ≤ 1`. -/
theorem proposition_3_3 {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) :
    ∫⁻ ω in {ω | σ ω ≠ ⊤},
        ENNReal.ofReal (stoppedValue (fun n ω => Q lam (T ℱ X P n ω) (S X n ω)) σ ω) ∂P ≤ 1 := by sorry

end FreedmanTail.Bernstein
