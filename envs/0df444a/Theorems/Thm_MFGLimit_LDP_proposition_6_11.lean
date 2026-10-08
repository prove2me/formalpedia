-- Prove2me | Theorems.Thm_MFGLimit_LDP_proposition_6_11
-- name    : MFGLimit.LDP.proposition_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:05.188993+00:00
-- url     : https://prove2.me/theorems/bc23dd9d-b7a4-4c42-b3cb-0cfab89c4131
-- title:
--   Proposition 6.11, p. 29 — level sets of J^{σ₀} + R(·₀|μ₀) are compact after centering; H¹ bound on 𝕄^ν − σ₀φ
-- statement:
--   Assume Condition 6.3 and that $\sigma$ is non-degenerate. For any $\sigma_0\ne0$ and $a\ge0$ there exist a compact $K\subset C([0,T];\mathcal P^1(\mathbb R^d))$ and $\kappa<\infty$ such that, for every $\nu$ with $J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)\le a$:
--
--   1. the centered flow $(\nu_t\circ\tau^{-1}_{\mathbb M^\nu_t})_{t\in[0,T]}$ lies in $K$;
--   2. for every $\phi\in\mathcal C^{d_0}_0$ with $I^{\sigma_0\phi}(\nu)\le a$, the path $(\mathbb M^\nu_t-\sigma_0\phi_t)_{t\in[0,T]}$ lies in $\mathcal H^1([0,T];\mathbb R^d)$ and
--   $$\|\mathbb M^\nu-\sigma_0\phi\|_{\mathcal H^1}<\kappa.$$
--
--   Level sets of $J^{\sigma_0}$ are not compact when $\sigma_0\ne0$, but they become so once the mean is removed.
--
--   **Formalization Note** $J^{\sigma_0}$ is the (6.9) form; $\mathbb M^\nu$ is the mean path (6.10).
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 29, Proposition 6.11

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

/-- Proposition 6.11, p. 29 (compactness after centering, `H¹` bound). -/
theorem proposition_6_11 {d d₀ : ℕ} (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (T : ℝ≥0) (hT : 0 < T) (hσ : σ.det ≠ 0) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (hb : DriftCond T btil)
    (μ₀ : Measure (MFGLimit.Conc.E d)) [IsProbabilityMeasure μ₀] (hexp : ExpMoments μ₀)
    (hσ₀ : σ₀ ≠ 0) (a : ℝ≥0) :
    ∃ K : Set (PathP1 d T), IsCompactD Dpath K ∧ ∃ κ : ℝ, ∀ ν : PathP1 d T,
      rateTilde σ σ₀ btil μ₀ ν ≤ a →
        (∃ ν' ∈ K, ν'.ν = shiftFlow ν.ν (meanPath ν.ν)) ∧
        ∀ φ : C0T d₀ T, Iphi σ btil (fun r => matVec σ₀ ((φ : CPath d₀ T).atR r)) ν.ν ≤ a →
          IsH1 T (fun r => meanPath ν.ν r - matVec σ₀ ((φ : CPath d₀ T).atR r)) ∧
            H1norm T (fun r => meanPath ν.ν r - matVec σ₀ ((φ : CPath d₀ T).atR r)) < κ := by sorry

end MFGLimit.LDP
