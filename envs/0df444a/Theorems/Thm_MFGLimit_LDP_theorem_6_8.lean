-- Prove2me | Theorems.Thm_MFGLimit_LDP_theorem_6_8
-- name    : MFGLimit.LDP.theorem_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:25.973466+00:00
-- url     : https://prove2.me/theorems/7eed3769-8965-45b5-ba78-92be26281e8c
-- title:
--   Theorem 6.8, p. 28 — the empirical flows of the weakly interacting system (6.1) satisfy a weak LDP with rate J̃^{σ₀,μ₀}
-- statement:
--   Consider the weakly interacting system (6.1)
--   $$d\tilde X^i_t=\tilde b(t,\tilde X^i_t,m^n_{\tilde{\boldsymbol X}_t})dt+\sigma dB^i_t+\sigma_0dW_t,\qquad \tilde X^i_0=X^i_0,$$
--   in the setting of §2.3, under Condition 6.3 and with $\sigma$ non-degenerate. Let $\tilde J^{\sigma_0,\mu_0}(\nu)=J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)$ (6.11) with $J^{\sigma_0}$ from (6.9). Then in $C([0,T];\mathcal P^1(\mathbb R^d))$:
--
--   1. for every open $O$, $\displaystyle\liminf_{n\to\infty}\frac1n\log\mathbb P(m^n_{\tilde{\boldsymbol X}}\in O)\ge-\inf_{\nu\in O}\tilde J^{\sigma_0,\mu_0}(\nu)$;
--   2. for every closed $F$,
--   $$\limsup_{n\to\infty}\frac1n\log\mathbb P(m^n_{\tilde{\boldsymbol X}}\in F)\le-\lim_{\delta\searrow0}\inf_{\nu\in F_\delta}\tilde J^{\sigma_0,\mu_0}(\nu),$$
--   with $F_\delta=\{\nu:\inf_{\tilde\nu\in F}\sup_t\mathcal W_1(\tilde\nu_t,\nu_t)\le\delta\}$.
--
--   **Formalization Note** The paper prints the lower bound without the minus sign; the intended (and here stated) bound is $\ge-\inf_O\tilde J^{\sigma_0,\mu_0}$, as in Theorem 3.10 and the proof on p. 34. Non-degeneracy of $\sigma$ (A(2), a standing assumption of the paper) is used through Lemma 6.17.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 28, Theorem 6.8

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

/-- Theorem 6.8, p. 28 (weak LDP for the weakly interacting system (6.1)). -/
theorem theorem_6_8 {d d₀ : ℕ} (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (T : ℝ≥0) (hT : 0 < T) (hσ : σ.det ≠ 0) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (hb : DriftCond T btil)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d)
    (μ₀ : Measure (MFGLimit.Conc.E d)) (hset : IsSetup 𝔽 P W B X₀ μ₀) (hexp : ExpMoments μ₀)
    (X : ∀ n, Fin n → Ω → CPath d T)
    (hX : ∀ n, IsInteractingSystem T 𝔽 P σ σ₀ W B X₀ btil (X n)) :
    LDPLower P (flowEvent X) Dpath (rateTilde σ σ₀ btil μ₀) ∧
      LDPUpperClosedDelta P (flowEvent X) Dpath (rateTilde σ σ₀ btil μ₀) := by sorry

end MFGLimit.LDP
