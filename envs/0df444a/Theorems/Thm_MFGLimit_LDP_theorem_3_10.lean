-- Prove2me | Theorems.Thm_MFGLimit_LDP_theorem_3_10
-- name    : MFGLimit.LDP.theorem_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:54.469489+00:00
-- url     : https://prove2.me/theorems/18ba38c4-817d-4f30-b418-8710a231f51e
-- title:
--   Theorem 3.10, p. 14 — with common noise, the Nash flows (m^n_{X_t})_t satisfy a weak LDP in C([0,T]; P¹(ℝ^d)) with rate J^{σ₀}(ν) + R(ν₀|μ₀)
-- statement:
--   Assume $p^*=1$, Assumption A and either Assumption B or B′, and
--
--   $$\int_{\mathbb R^d}\exp(\lambda|x|)\,\mu_0(dx)<\infty\quad\text{for all }\lambda>0.$$
--
--   Let $\tilde b(t,x,m)=\hat b(x,m,D_xU(t,x,m))$ (3.10), assumed bounded, and $J^{\sigma_0}(\nu)=\tilde I^{\mathbb M^{\tilde b,\nu}}((\nu_t\circ\tau^{-1}_{\mathbb M^{\tilde b,\nu}_t})_{t\in[0,T]})$ the rate functional of p. 14. Then the Nash equilibrium empirical measure flows $(m^n_{\boldsymbol X_t},t\in[0,T])_{n\in\mathbb N}$ of (2.7) satisfy the weak large deviation principle in $C([0,T];\mathcal P^1(\mathbb R^d))$ (uniform $\mathcal W_1$ topology):
--
--   1. for every open $O$: $\displaystyle\liminf_{n\to\infty}\frac1n\log\mathbb P(m^n_{\boldsymbol X_\cdot}\in O)\ge-\inf_{\nu\in O}\big(J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)\big)$;
--   2. for every compact $K$: $\displaystyle\limsup_{n\to\infty}\frac1n\log\mathbb P(m^n_{\boldsymbol X_\cdot}\in K)\le-\inf_{\nu\in K}\big(J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)\big)$;
--   3. for every closed $F$:
--   $$\limsup_{n\to\infty}\frac1n\log\mathbb P(m^n_{\boldsymbol X_\cdot}\in F)\le-\lim_{\delta\searrow0}\inf_{\nu\in F_\delta}\big(J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)\big),$$
--   where $F_\delta=\{\nu:\inf_{\tilde\nu\in F}\sup_{t}\mathcal W_1(\tilde\nu_t,\nu_t)\le\delta\}$.
--
--   This is the first large deviation principle for mean field game equilibria with common noise.
--
--   **Formalization Note** The boundedness of $\tilde b$ is added to the printed hypotheses: the proof goes through Theorem 6.8, whose Condition 6.3(2) requires it, and Assumption A does not imply it. $\tilde b$ is evaluated on $\mathcal P^1$, where A(5) (with $p^*=1$) provides $D_xU$. The Nash-system solutions $v^{n,i}$, the master-equation solution $U$ and the state processes are hypotheses.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 14, Theorem 3.10 (rate functional defined on p. 14)

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

/-- Theorem 3.10, p. 14 (weak LDP for the Nash equilibrium flows, common noise allowed). -/
theorem theorem_3_10 {d d₀ : ℕ} {A : Type*} [TopologicalSpace A] [PolishSpace A]
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
    LDPLower P (flowEvent X) Dpath (rateExplicit M.σ M.σ₀ (btilOf M U) μ₀) ∧
      LDPUpperCompact P (flowEvent X) Dpath (rateExplicit M.σ M.σ₀ (btilOf M U) μ₀) ∧
      LDPUpperClosedDelta P (flowEvent X) Dpath (rateExplicit M.σ M.σ₀ (btilOf M U) μ₀) := by sorry

end MFGLimit.LDP
