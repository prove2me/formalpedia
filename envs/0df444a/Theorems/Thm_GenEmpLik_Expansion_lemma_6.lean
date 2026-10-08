-- Prove2me | Theorems.Thm_GenEmpLik_Expansion_lemma_6
-- name    : GenEmpLik.Expansion.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:26:21.872852+00:00
-- url     : https://prove2.me/theorems/1490afc7-73b5-4704-8ab9-3525038c9837
-- title:
--   Lemma 6 — on the event $\mathcal E_n$ the robust mean lies within $\sqrt{\rho s_n^2/n}\,(1\pm C\epsilon)^{-1/2}$ of the sample mean
-- statement:
--   Let $f$ satisfy Assumption A, $n\ge1$, $\rho>0$, $0<\epsilon<1$, and let $C\ge0$ with $C\epsilon<1$ be such that the sandwich (30) holds at $\epsilon$: $2(1-C\epsilon)h_\epsilon(t)\le f(t+1)$ for $t\ge-1$ and $f(t+1)\le(1+C\epsilon)t^2$ for $|t|\le\epsilon$. Let $z=(z_1,\dots,z_n)$ be a sample with empirical distribution $\widehat P_n$, mean $\bar z_n=E_{\widehat P_n}[Z]$ and variance $s_n^2=E_{\widehat P_n}[Z^2]-E_{\widehat P_n}[Z]^2$. If the event
--
--   $$
--   \mathcal E_n:\quad \max_{i\le n}\frac{|z_i-\bar z_n|}{\sqrt n}\le\epsilon\, s_n\sqrt{\frac{1-C\epsilon}{\rho}}
--   $$
--
--   holds, then
--
--   $$
--   E_{\widehat P_n}[Z]+\sqrt{\frac\rho n s_n^2}\,\frac{1}{\sqrt{1+C\epsilon}}\;\le\;\sup_{P:\,D_f(P\|\widehat P_n)\le\rho/n}E_P[Z]\;\le\;E_{\widehat P_n}[Z]+\sqrt{\frac\rho n s_n^2}\,\frac{1}{\sqrt{1-C\epsilon}} .
--   $$
--
--   Since $\mathcal E_n$ holds eventually almost surely for a stationary ergodic sequence with finite variance, and $\epsilon$ can be taken arbitrarily small, this yields the variance expansion (Lemma 1).
--
--   **Formalization Note** The statement is deterministic: "on $\mathcal E_n$" is the event's inequality as a hypothesis on the sample vector. The paper's $C$ is the constant of (30) and its $\epsilon$ is at most the $c$ of (30); here the two inequalities of (30) at $\epsilon$ and $C$ are hypotheses. The paper allows $\epsilon=0$, where $h_\epsilon$ is undefined; the statement takes $\epsilon>0$. The hypothesis $C\epsilon<1$ is implicit in the paper's $\sqrt{1-C\epsilon}$. Sample mean and variance are the published `empMean`, `empVar`; the robust mean is `robustMean`.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 31, Lemma 6

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_AssumptionA
import Definitions.Def_GenEmpLik_Expansion_huber
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar

open VarianceRegularization.Expansion

namespace GenEmpLik.Expansion

/-- Lemma 6 (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 31), deterministic form. Let `C`
be a constant for which the two inequalities of (30) hold at `ε`, with `0 < ε < 1`, `0 ≤ C`,
`Cε < 1`. On the event `ℰ_n = {max_{i ≤ n} |zᵢ − z̄_n| / √n ≤ ε s_n √((1 − Cε)/ρ)}`,
`E_{P̂n}[Z] + √(ρ/n · s_n²) / √(1 + Cε) ≤ sup_{P : D_f(P‖P̂n) ≤ ρ/n} E_P[Z]
  ≤ E_{P̂n}[Z] + √(ρ/n · s_n²) / √(1 − Cε)`. -/
theorem lemma_6 (f : ℝ → EReal) (hA : AssumptionA f) {n : ℕ} (hn : 0 < n) {ρ ε C : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 ≤ C) (hCε : C * ε < 1)
    (hlow : ∀ t : ℝ, -1 ≤ t → ((2 * (1 - C * ε) * huber ε t : ℝ) : EReal) ≤ f (t + 1))
    (hup : ∀ t : ℝ, |t| ≤ ε → f (t + 1) ≤ (((1 + C * ε) * t ^ 2 : ℝ) : EReal))
    (z : Fin n → ℝ)
    (hE : (⨆ i, |z i - empMean z|) / Real.sqrt n ≤
      ε * Real.sqrt (empVar z) * Real.sqrt ((1 - C * ε) / ρ)) :
    empMean z + Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 + C * ε)) ≤
        robustMean f ρ z ∧
      robustMean f ρ z ≤
        empMean z + Real.sqrt (ρ / n * empVar z) * (1 / Real.sqrt (1 - C * ε)) := by sorry

end GenEmpLik.Expansion
