-- Prove2me | Theorems.Thm_MFGLimit_LDP_lemma_6_17
-- name    : MFGLimit.LDP.lemma_6_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:42.213187+00:00
-- url     : https://prove2.me/theorems/353175bb-5dc6-4144-8d9a-1e157c29d5ed
-- title:
--   Lemma 6.17, p. 35 — inf_{Q: Φ(Q,φ)=ν} R(Q | μ₀ × 𝕎) = Ĩ^{σ₀φ}((ν_t ∘ τ⁻¹_{σ₀φ_t})_t) + R(ν₀ | μ₀)
-- statement:
--   Assume Condition 6.3 and that $\sigma$ is non-degenerate; let $\mathbb W$ be the Wiener measure on $\mathcal C^d_0$ and $\Phi$ the McKean–Vlasov map of §6.3.2. For every $\nu\in C([0,T];\mathcal P^1(\mathbb R^d))$ and every $\phi\in\mathcal C^{d_0}_0$,
--
--   $$\inf_{\mathcal Q\in\mathcal P^1(\mathbb R^d\times\mathcal C^d_0):\ \Phi(\mathcal Q,\phi)=\nu}\mathcal R(\mathcal Q|\mu_0\times\mathbb W)=\tilde I^{\sigma_0\phi}\big((\nu_t\circ\tau^{-1}_{\sigma_0\phi_t})_{t\in[0,T]}\big)+\mathcal R(\nu_0|\mu_0).$$
--
--   The infimum over an empty set is $+\infty$. Combined with Proposition 6.15 and Lemma 6.16 this identifies the rate function of Theorem 6.8.
--
--   **Formalization Note** $\phi$ is a $d_0$-dimensional path (the paper writes $\mathcal C^d_0$). Relative entropies are Mathlib's `klDiv`, valued in $[0,\infty]$.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 35, Lemma 6.17

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model
import Definitions.Def_MFGLimit_LDP_MeasureDeriv
import Definitions.Def_MFGLimit_LDP_Equations
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_MFGLimit_LDP_PathSpace
import Definitions.Def_MFGLimit_LDP_Action
import Definitions.Def_MFGLimit_LDP_Contraction

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

/-- Lemma 6.17, p. 35 (identification of the contracted relative entropy). -/
theorem lemma_6_17 {d d₀ : ℕ} (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (T : ℝ≥0) (hT : 0 < T) (hσ : σ.det ≠ 0) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (hb : DriftCond T btil)
    (μ₀ : Measure (MFGLimit.Conc.E d)) [IsProbabilityMeasure μ₀] (hexp : ExpMoments μ₀)
    (𝕎 : Measure (C0T d T)) [IsProbabilityMeasure 𝕎] (h𝕎 : IsWienerMeasure d T 𝕎)
    (sol : Measure (MFGLimit.Conc.E d × C0T d T) → C0T d₀ T → MFGLimit.Conc.E d × C0T d T → CPath d T)
    (hsol : IsMVSolutionMap σ σ₀ btil sol) (ν : PathP1 d T) (φ : C0T d₀ T) :
    (⨅ (z : QPhi d d₀ T) (_ : z.φ = φ ∧ PhiMap sol z = ν.ν),
        InformationTheory.klDiv z.Q (μ₀.prod 𝕎)) =
      Itil σ btil (fun r => matVec σ₀ ((φ : CPath d₀ T).atR r)) (shiftFlow ν.ν (fun r => matVec σ₀ ((φ : CPath d₀ T).atR r)))
        + InformationTheory.klDiv (ν.ν (t0 T)) μ₀ := by sorry

end MFGLimit.LDP
