-- Prove2me | Theorems.Thm_MFGLimit_LDP_theorem_6_6
-- name    : MFGLimit.LDP.theorem_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:51.58717+00:00
-- url     : https://prove2.me/theorems/e6d7e9ed-1ed3-44c9-857b-8a710f6ed5b3
-- title:
--   Theorem 6.6, p. 27 — J^{σ₀}(ν) = Ĩ^{𝕄^{b̃,ν}}((ν_t ∘ τ⁻¹_{𝕄^{b̃,ν}_t})_t) if σ₀ ≠ 0, and I⁰(ν) if σ₀ = 0
-- statement:
--   Assume Condition 6.3(2) on $\tilde b$ and that $\sigma$ is non-degenerate. For $\nu\in C([0,T];\mathcal P^1(\mathbb R^d))$ with mean path $\mathbb M^\nu$ (6.10), let
--   $$\mathbb M^{\tilde b,\nu}_t=\sigma\Pi_{\sigma^{-1}\sigma_0}\sigma^{-1}\Big(\mathbb M^\nu_t-\mathbb M^\nu_0-\int_0^t\langle\nu_s,\tilde b(s,\cdot,\nu_s)\rangle ds\Big),\qquad t\in[0,T].$$
--   Then $J^{\sigma_0}$ of (6.9) satisfies
--
--   $$J^{\sigma_0}(\nu)=\begin{cases}\tilde I^{\mathbb M^{\tilde b,\nu}}\big((\nu_t\circ\tau^{-1}_{\mathbb M^{\tilde b,\nu}_t})_{t\in[0,T]}\big)&\text{if }\sigma_0\ne0,\\ I^0(\nu)&\text{if }\sigma_0=0.\end{cases}$$
--
--   This identifies the infimum (6.9) with the explicit rate function used in Theorem 3.10.
--
--   **Formalization Note** The infimum form (6.9) and the explicit p. 14 form are separate definitions (`Jinf`, `Jexplicit`).
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 27, Theorem 6.6

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

/-- Theorem 6.6, p. 27 (the explicit form of `J^{σ₀}`). -/
theorem theorem_6_6 {d d₀ : ℕ} (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (T : ℝ≥0) (hT : 0 < T) (hσ : σ.det ≠ 0) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (hb : DriftCond T btil) (ν : PathP1 d T) :
    (σ₀ ≠ 0 → Jinf σ σ₀ btil ν.ν = Jexplicit σ σ₀ btil ν.ν) ∧
      (σ₀ = 0 → Jinf σ σ₀ btil ν.ν = IphiH1 σ btil (fun _ => 0) ν.ν) := by sorry

end MFGLimit.LDP
