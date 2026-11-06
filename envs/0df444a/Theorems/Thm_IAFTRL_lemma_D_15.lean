-- Prove2me | Theorems.Thm_IAFTRL_lemma_D_15
-- name    : IAFTRL.lemma_D_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:24.743101+00:00
-- url     : https://prove2.me/theorems/be9a6bdd-4bf8-473e-8d9a-4d36a20f7d92
-- title:
--   Lemma D.15 — conditional identities of the executed loss-difference estimates
-- statement:
--   Consider an execution of IA-FTRL for $T$ rounds, a round $t<T$ and actions $a,c$, and let
--   $$
--   g_{t,a}=(a-r_t)^\top v_{t,A_t}Y_t .
--   $$
--   Then $g_{t,a}$ and $g_{t,a}^2$ are integrable and, with $\mathbb E_{t-1}$ the conditional expectation given the pre-action σ-algebra $\mathcal G_t$,
--   $$
--   \mathbb E_{t-1}[g_{t,a}]=(a-r_t)^\top\theta_t,\qquad \mathbb E_{t-1}[g_{t,a}-g_{t,c}]=(a-c)^\top\theta_t,
--   $$
--   $$
--   \mathbb E_{t-1}[g_{t,a}^2]\le\beta_t+\frac{Z_{t,a}^2}{Bt},\qquad |g_{t,a}|\le\beta_t+\frac{Z_{t,a}}{B},
--   $$
--   the first three almost surely and the last on every outcome.
--
--   The executed estimates are conditionally unbiased for the loss differences and obey the program's moment and magnitude budgets; these identities enter the regret decomposition and the moment analysis.
--
--   **Formalization Note** Rounds are 0-based: the Lean round $t$ uses $\beta_{t+1}$, $Z_{t+1}$ and $B(t+1)$. Since the right-hand sides are $\mathcal F_{t-1}$-measurable, the identities given $\mathcal F_{t-1}$ follow by the tower property.
--
--   Differences from the source:
--   - reading: $\mathbb E_{t-1}$ → conditional expectation given the pre-action σ-algebra $\mathcal G_t\supseteq\mathcal F_{t-1}\vee\sigma(\theta_t)$; reason: Appendix J.1 (p.204) enlarges the pre-action filtration; the right-hand sides are $\mathcal F_{t-1}$-measurable, so this also gives the identities given $\mathcal F_{t-1}$
--   - encoding: conditional expectations → integrability of $g_{t,a}$ and $g_{t,a}^2$ added to the conclusion; reason: guards Lean's junk conditional expectation; true by Lemma D.1
--   - encoding: paper rounds $t=1,\dots,T$ → 0-based Lean rounds $t<T$, Lean round $t$ using $\beta_{t+1}$, $q_{t+1}$, $Z_{t+1}$; reason: Lean indexing convention; same instances
--   - encoding: dimension $d$ of $\mathbb R^d$ → $d\ge1$; reason: the paper works in $\mathbb R^d$ with a spanning action set in the unit ball; only the degenerate $d=0$ is excluded
--   - reading: protocol $\mathbb E[Y_t\mid\mathcal F_{t-1},\theta_t,A_t]=A_t^\top\theta_t$, $A_t\sim p_t$ → action law given $\mathcal G_t$, feedback identity given $\mathcal G_t\vee\sigma(A_t)$, for the pre-action filtration $\mathcal G_t$; reason: Appendix J.1, p.204: "Enlarging the pre-action filtration to include an environment\'s fresh pre-action randomization does not reveal it to the learner"
--   - reading: IA-FTRL with "a fixed $\mathcal F_{t-1}$-measurable rule" for $p_t$ → every $\mathcal F_{t-1}$-measurable minimizer of (2.3); reason: p.17 leaves the rule open ("e.g., the lexicographically smallest"); the lemma uses only feasibility of $p_t$
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix D.6.2, Lemma D.15, p.88

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_Run_gEst
import Definitions.Def_IAFTRL_Bc

namespace IAFTRL

open Matrix MeasureTheory

/-- **Lemma D.15 (Executed reconstruction and conditional estimator identities).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299,
Lemma D.15, p.88: "For IA-FTRL, define `g_{t,a} = (a − r_t)^⊤v_{t,A_t}Y_t`. Then
`E_{t−1}[g_{t,a}] = (a − r_t)^⊤θ_t`, `E_{t−1}[(g_{t,a} − g_{t,c})] = (a − c)^⊤θ_t`,
`E_{t−1}[g²_{t,a}] ≤ β_t + Z²_{t,a}/(Bt)`, `|g_{t,a}| ≤ β_t + Z_{t,a}/B`."

For every execution of IA-FTRL for `T` rounds (spanning finite action set in the unit ball of
`ℝ^d`, `d ≥ 1`), every round `t < T` (paper round `t + 1`) and all actions `a, c`, with
`g_{t,a} = (a − r_t)^⊤ v_{t,A_t} Y_t`:
1. `g_{t,a}` and `g²_{t,a}` are integrable;
2. `E[g_{t,a} | G_t] = (a − r_t)^⊤θ_t` a.s.;
3. `E[g_{t,a} − g_{t,c} | G_t] = (a − c)^⊤θ_t` a.s.;
4. `E[g²_{t,a} | G_t] ≤ β_{t+1} + Z²_{t+1,a}/(B(t+1))` a.s.;
5. `|g_{t,a}| ≤ β_{t+1} + Z_{t+1,a}/B` everywhere.

**Formalization Note.** `E_{t−1}` is conditioning on the pre-action σ-algebra `G_t` (p.204), which
contains `F_{t−1}` and `θ_t`. Since the right-hand sides are `F_{t−1}`-measurable, the identities
conditional on `F_{t−1}` follow by the tower property. Integrability is stated so that the
conditional expectations are not Mathlib's junk value. 0-based round `t` uses `β_{t+1}`,
`Z_{t+1}` and `B(t+1)`. -/
theorem lemma_D_15 {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t < T) (a c : Fin K) :
    Integrable (R.gEst arms t a) P ∧ Integrable (fun ω => R.gEst arms t a ω ^ 2) P ∧
    P[R.gEst arms t a | R.G t] =ᵐ[P]
      (fun ω => (arms a - refArm arms (R.cumEst arms t ω)) ⬝ᵥ R.θs t ω) ∧
    P[fun ω => R.gEst arms t a ω - R.gEst arms t c ω | R.G t] =ᵐ[P]
      (fun ω => (arms a - arms c) ⬝ᵥ R.θs t ω) ∧
    P[fun ω => R.gEst arms t a ω ^ 2 | R.G t] ≤ᵐ[P]
      (fun ω => beta d K (t + 1) + Zd arms (R.cumEst arms t ω) a ^ 2 / (Bc K * (t + 1))) ∧
    ∀ ω, |R.gEst arms t a ω| ≤ beta d K (t + 1) + Zd arms (R.cumEst arms t ω) a / Bc K := by sorry

end IAFTRL
