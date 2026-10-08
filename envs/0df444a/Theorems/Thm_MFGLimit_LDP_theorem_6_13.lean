-- Prove2me | Theorems.Thm_MFGLimit_LDP_theorem_6_13
-- name    : MFGLimit.LDP.theorem_6_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:39.609476+00:00
-- url     : https://prove2.me/theorems/d05df4d6-5c91-4511-bcb9-14509e563552
-- title:
--   Theorem 6.13, p. 30 — the Nash equilibrium flows m^n_X satisfy the weak LDP of Theorem 6.8 with rate J̃^{σ₀,μ₀}
-- statement:
--   Let Assumption A and either Assumption B or B′ hold with $p^*=1$, let the initial law $\mu_0$ satisfy (6.2), and let $\tilde b(t,x,m)=\hat b(x,m,D_xU(t,x,m))$ be bounded. Then the empirical measure flows $(m^n_{\boldsymbol X})_{n\ge1}$ of the Nash equilibrium state processes (2.7) satisfy, in $C([0,T];\mathcal P^1(\mathbb R^d))$,
--
--   $$\liminf_{n\to\infty}\frac1n\log\mathbb P(m^n_{\boldsymbol X}\in O)\ge-\inf_{\nu\in O}\tilde J^{\sigma_0,\mu_0}(\nu),\qquad \limsup_{n\to\infty}\frac1n\log\mathbb P(m^n_{\boldsymbol X}\in F)\le-\lim_{\delta\searrow0}\inf_{\nu\in F_\delta}\tilde J^{\sigma_0,\mu_0}(\nu)$$
--
--   for every open $O$ and every closed $F$, with $\tilde J^{\sigma_0,\mu_0}$ from (6.11).
--
--   **Formalization Note** Two hypotheses are added to the printed statement: $p^*=1$ (needed by Corollary 6.1, on which the proof rests, and stated in Theorem 3.10) and the boundedness of $\tilde b$ (Condition 6.3(2), needed by Theorem 6.8; Assumption A gives continuity and the Lipschitz property of $\tilde b$ but not boundedness).
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 30, Theorem 6.13

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

/-- Theorem 6.13, p. 30 (weak LDP for the Nash flows with the rate function (6.11)). -/
theorem theorem_6_13 {d d₀ : ℕ} {A : Type*} [TopologicalSpace A] [PolishSpace A]
    [MeasurableSpace A] [BorelSpace A] (M : Model d d₀ A) (T : ℝ≥0) (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d)
    (μ₀ : Measure (MFGLimit.Conc.E d)) (hset : IsSetup 𝔽 P W B X₀ μ₀)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → MFGLimit.Conc.E d) → ℝ) (U : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ)
    (hp : M.pStar = 1) (hA : AssumptionA M T μ₀ v U)
    (hB : AssumptionB M ∨ AssumptionB' M T v U)
    (hexp : ExpMoments μ₀)
    (hbdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m, MFGLimit.Conc.IsPp 1 m → ‖btilOf M U t x m‖ ≤ C)
    (X : ∀ n, Fin n → Ω → CPath d T) (hX : ∀ n, IsNashState M T 𝔽 P W B X₀ (v n) (X n)) :
    LDPLower P (flowEvent X) Dpath (rateTilde M.σ M.σ₀ (btilOf M U) μ₀) ∧
      LDPUpperClosedDelta P (flowEvent X) Dpath (rateTilde M.σ M.σ₀ (btilOf M U) μ₀) := by sorry

end MFGLimit.LDP
