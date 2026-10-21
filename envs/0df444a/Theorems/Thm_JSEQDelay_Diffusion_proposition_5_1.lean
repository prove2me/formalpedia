-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_proposition_5_1
-- name    : JSEQDelay.Diffusion.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:51.944886+00:00
-- url     : https://prove2.me/theorems/fcd3be74-7ff9-4123-b306-5f63677799e8
-- title:
--   Proposition 5.1, p. 17 — under Assumptions 3.1 and 3.9 the diffusion model has at most one solution
-- statement:
--   Let the delay function $\tau$ satisfy Assumption 3.1 and let the limiting estimator $\hat\Psi$ satisfy the contraction property of Assumption 3.9. Let $\hat X,\hat S$ be the limiting Brownian motions, built from constants $\bar\lambda,\bar\mu_k>0$ with $\langle\bar\mu,\mathbf 1\rangle=\bar\lambda$, $\hat\lambda,\hat\mu_k\in\mathbb R$, $\alpha,\gamma_k>0$. If $(\hat Q,\hat A)$ and $(\hat Q',\hat A')$ are solutions of the diffusion model associated with $(\hat X,\hat S,\hat\Phi)$, then almost surely
--   $$(\hat Q(t),\hat A(t))=(\hat Q'(t),\hat A'(t))\qquad\text{for all }t\ge0.$$
--
--   This is the uniqueness half of Theorem 4.4: together with tightness it identifies every subsequential limit of the scaled network.
--
--   **Formalization Note** "At most one solution" is read as indistinguishability on $[0,\infty)$. The limiting estimator is required to be a limiting estimator in the sense of p. 12 (measurable, continuous, nonanticipating); only the heavy-traffic constants that enter $(\hat X,\hat S)$ are assumed.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 17, Proposition 5.1

import Mathlib
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_JSEQDelay_Diffusion_Model
import Definitions.Def_JSEQDelay_Diffusion_Assumptions
import Definitions.Def_JSEQDelay_Diffusion_DiffusionModel

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open RankBasedSDI.LoadBalancing

/-- **Proposition 5.1** (p. 17): if the delay function satisfies Assumption 3.1 and the
limiting estimator `Ψ̂` satisfies the contraction property of Assumption 3.9, the diffusion
model associated with `(X̂, Ŝ, Φ̂)` has at most one solution: any two solutions agree almost
surely at all times `t ≥ 0`. -/
theorem proposition_5_1 {K : ℕ} (hK : 2 ≤ K)
    (τ : ℝ → Fin K → ℝ) (hτ : Assumption31 τ)
    (PsiLim : Path K → Path K → Path K) (hlim : IsLimitEstimator τ PsiLim)
    (h39 : Assumption39 τ PsiLim)
    (lamBar lamHat : ℝ) (muBar muHat : Fin K → ℝ) (hpar : LimitParams lamBar muBar)
    (α : ℝ) (γ : Fin K → ℝ) (hα : 0 < α) (hγ : ∀ k, 0 < γ k)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : Ω' → ℝ → Fin (K + 1) → ℝ) (hW : IsStandardBM P' W)
    (Q₁ A₁ Q₂ A₂ : Ω' → Path K)
    (h₁ : IsDiffusionSolution P' (limX lamBar lamHat muHat α W) (limS muBar γ W) τ PsiLim Q₁ A₁)
    (h₂ : IsDiffusionSolution P' (limX lamBar lamHat muHat α W) (limS muBar γ W) τ PsiLim Q₂ A₂) :
    ∀ᵐ ω ∂P', ∀ t, 0 ≤ t → Q₁ ω t = Q₂ ω t ∧ A₁ ω t = A₂ ω t := by sorry

end JSEQDelay.Diffusion
