-- Prove2me | Theorems.Thm_MFGLimit_LDP_proposition_6_5
-- name    : MFGLimit.LDP.proposition_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:19.116415+00:00
-- url     : https://prove2.me/theorems/a5c11f82-2f90-439a-830a-7e6024cb95ac
-- title:
--   Proposition 6.5, p. 27 — if 𝕄^ν ∈ H¹, J^{σ₀}(ν) = I⁰(ν) − ½∫₀ᵀ |Π_{σ⁻¹σ₀}σ⁻¹(𝕄̇^ν_t − ⟨ν_t, b̃(t,·,ν_t)⟩)|² dt
-- statement:
--   Assume Condition 6.3(2) on $\tilde b$ and that $\sigma$ is non-degenerate. Let $\nu\in C([0,T];\mathcal P^1(\mathbb R^d))$ have mean path $\mathbb M^\nu\in\mathcal H^1([0,T];\mathbb R^d)$. Then, with $I^0$ from (6.4) ($\phi=0$) and $J^{\sigma_0}$ from (6.9),
--
--   $$J^{\sigma_0}(\nu)=I^0(\nu)-\frac12\int_0^T\Big|\Pi_{\sigma^{-1}\sigma_0}\sigma^{-1}\big(\dot{\mathbb M}^\nu_t-\langle\nu_t,\tilde b(t,\cdot,\nu_t)\rangle\big)\Big|^2dt.$$
--
--   The common noise lowers the cost by the energy of the mean drift in the directions of the image of $\sigma^{-1}\sigma_0$.
--
--   **Formalization Note** The identity is stated in the equivalent form $J^{\sigma_0}(\nu)+\frac12\int_0^T|\cdots|^2dt=I^0(\nu)$ in $[0,\infty]$, which avoids truncated subtraction; the subtracted integral is finite under the hypotheses ($\dot{\mathbb M}^\nu\in L^2$, $\tilde b$ bounded).
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 27, Proposition 6.5

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

/-- Proposition 6.5, p. 27 (`J^{σ₀}` for paths with an `H¹` mean path). -/
theorem proposition_6_5 {d d₀ : ℕ} (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (T : ℝ≥0) (hT : 0 < T) (hσ : σ.det ≠ 0) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (hb : DriftCond T btil) (ν : PathP1 d T) (hM : IsH1 T (meanPath ν.ν)) :
    Jinf σ σ₀ btil ν.ν
        + (1 / 2 : ℝ≥0∞) * ∫⁻ t in Set.Icc (0 : ℝ) T,
            ‖projRange σ σ₀ (matVec σ⁻¹ (deriv (meanPath ν.ν) t
              - ∫ x, btil t.toNNReal x (flowAt ν.ν t) ∂(flowAt ν.ν t)))‖ₑ ^ 2 =
      IphiH1 σ btil (fun _ => 0) ν.ν := by sorry

end MFGLimit.LDP
