-- Prove2me | Theorems.Thm_MFGLimit_LDP_corollary_6_1
-- name    : MFGLimit.LDP.corollary_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:30.421248+00:00
-- url     : https://prove2.me/theorems/e7796d2c-fe83-4e29-91d6-58f65451493d
-- title:
--   Corollary 6.1, p. 24 — lim (1/n) log P(sup_t W₂(m^n_{X_t}, m^n_{X̄_t}) > ε) = −∞ (exponential equivalence)
-- statement:
--   Let Assumption A and either Assumption B or B′ hold, with $p^*=1$. Let $\boldsymbol X^n=(X^1,\dots,X^n)$ be the Nash equilibrium state process (2.7) and $\bar{\boldsymbol X}^n=(\bar X^1,\dots,\bar X^n)$ the McKean–Vlasov particle system (4.1), driven by the same noises and initial states. Then for every $\epsilon>0$,
--
--   $$\lim_{n\to\infty}\frac1n\log\mathbb P\Big(\sup_{t\in[0,T]}\mathcal W_2(m^n_{\boldsymbol X_t},m^n_{\bar{\boldsymbol X}_t})>\epsilon\Big)=-\infty.$$
--
--   The empirical measure flows of the Nash system and of the particle system are exponentially equivalent; large deviation bounds transfer from one to the other.
--
--   **Formalization Note** The limit is taken in $[-\infty,\infty]$. The solution families of (2.6), (2.8), (2.7), (4.1) are hypotheses.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 24, Corollary 6.1

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model
import Definitions.Def_MFGLimit_LDP_MeasureDeriv
import Definitions.Def_MFGLimit_LDP_Equations
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_MFGLimit_LDP_PathSpace
import Definitions.Def_MFGLimit_LDP_Action

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

/-- Corollary 6.1, p. 24 (exponential equivalence of the Nash and McKean–Vlasov flows). -/
theorem corollary_6_1 {d d₀ : ℕ} {A : Type*} [TopologicalSpace A] [PolishSpace A]
    [MeasurableSpace A] [BorelSpace A] (M : Model d d₀ A) (T : ℝ≥0) (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d)
    (μ₀ : Measure (MFGLimit.Conc.E d)) (hset : IsSetup 𝔽 P W B X₀ μ₀)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → MFGLimit.Conc.E d) → ℝ) (U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ)
    (hp : M.pStar = 1) (hA : AssumptionA M T μ₀ v U)
    (hB : AssumptionB M ∨ AssumptionB' M T v U)
    (X Xbar : ∀ n, Fin n → Ω → CPath d T)
    (hX : ∀ n, IsNashState M T 𝔽 P W B X₀ (v n) (X n))
    (hXbar : ∀ n, IsMVParticle M T 𝔽 P W B X₀ U (Xbar n)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => scaledLog n (P {ω | ENNReal.ofReal ε <
          ⨆ t : Set.Icc (0 : ℝ≥0) T, Wp 2 (empMeas (fun i => X n i ω t))
            (empMeas (fun i => Xbar n i ω t))})) atTop (𝓝 ⊥) := by sorry

end MFGLimit.LDP
