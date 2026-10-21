-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_theorem_4_4
-- name    : JSEQDelay.Diffusion.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:05.28954+00:00
-- url     : https://prove2.me/theorems/99a1c57c-694b-48af-9e94-bc4e5c4b44e6
-- title:
--   Theorem 4.4, p. 17 — under Assumptions 3.1, 3.5, 3.8, 3.9 the diffusion model has a unique solution and (Q̂ⁿ, Âⁿ) ⇒ (Q̂, Â)
-- statement:
--   Consider the sequence of JSEQ networks with delayed information under the primitives of §2.1 and heavy traffic (Assumption 2.2). Suppose the delay function $\tau$ satisfies Assumption 3.1, and the scaled estimators $\hat\Psi^n$ and the limiting estimator $\hat\Psi$ satisfy the convergence condition (Assumption 3.5), the modulus of continuity condition (Assumption 3.8) and the contraction property (Assumption 3.9). Let $\hat X,\hat S$ be the limiting Brownian motions on a probability space $(\Omega',\mathbb P')$. Then:
--
--   1. the diffusion model associated with $(\hat X,\hat S,\hat\Phi)$ has a solution $(\hat Q,\hat A)$;
--   2. any two solutions agree almost surely at all times $t\ge0$;
--   3. for the solution,
--   $$(\hat Q^n,\hat A^n)\Rightarrow(\hat Q,\hat A)\qquad(n\to\infty),$$
--   jointly, in distribution on the space of $\mathbb R^{2K}$-valued paths.
--
--   The theorem is the paper's main result: the scaled queue lengths and routings of JSEQ under delayed information converge to a diffusion in which the estimated queue lengths, not the actual ones, are equal.
--
--   **Formalization Note** Convergence in distribution is the published coupling form `CouplingConverges`, applied to the concatenated $2K$-dimensional process, and is asserted for every solution (equivalent given uniqueness). The diffusion model lives on any probability space with a standard $(K+1)$-dimensional Brownian motion. The estimators act on real-valued paths, the network is required on the probability-one event where counts are finite, and Assumption 3.8's remainder may depend on $T$ (see the definitions). The proof in §5.4 obtains the limit on a Skorokhod-representation space; existence on the given space is part of the statement as printed.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 17, Theorem 4.4

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_JSEQDelay_Diffusion_Model
import Definitions.Def_JSEQDelay_Diffusion_Assumptions
import Definitions.Def_JSEQDelay_Diffusion_DiffusionModel

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-- **Theorem 4.4** (p. 17): suppose the delay function satisfies Assumption 3.1, and the
scaled estimators `Ψ̂ⁿ` and the limiting estimator `Ψ̂` satisfy Assumptions 3.5, 3.8 and 3.9.
Then the diffusion model associated with `(X̂, Ŝ, Φ̂)` has a solution, any two solutions agree
almost surely at all times `t ≥ 0`, and the diffusion-scaled queue lengths and routed arrivals
`(Q̂ⁿ, Âⁿ)` of the JSEQ networks converge jointly in distribution to the solution `(Q̂, Â)`. -/
theorem theorem_4_4 {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (α : ℝ) (γ : Fin K → ℝ)
    (hprim : Primitives P u v α γ)
    (lam : ℕ → ℝ) (mu : ℕ → Fin K → ℝ) (lamBar lamHat : ℝ) (muBar muHat : Fin K → ℝ)
    (hrates : Rates lam mu) (hHT : HeavyTraffic lam mu lamBar lamHat muBar muHat)
    (τ : ℝ → Fin K → ℝ) (hτ : Assumption31 τ)
    (Ψ : ℕ → Path K → Path K → Path K) (hΨ : ∀ n, IsEstimator τ (Ψ n))
    (PsiLim : Path K → Path K → Path K) (hlim : IsLimitEstimator τ PsiLim)
    (h35 : Assumption35 (fun n => PsiHat n (mu n) (Ψ n)) PsiLim)
    (h38 : Assumption38 τ (fun n => PsiHat n (mu n) (Ψ n)))
    (h39 : Assumption39 τ PsiLim)
    (Q A : ℕ → Ω → Path K)
    (hnet : ∀ n, 1 ≤ n → IsJSEQNetwork u v (lam n) (mu n) τ (Ψ n) (Q n) (A n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : Ω' → ℝ → Fin (K + 1) → ℝ) (hW : IsStandardBM P' W) :
    (∃ Qh Ah : Ω' → Path K, IsDiffusionSolution P' (limX lamBar lamHat muHat α W)
      (limS muBar γ W) τ PsiLim Qh Ah) ∧
    (∀ Q₁ A₁ Q₂ A₂ : Ω' → Path K,
      IsDiffusionSolution P' (limX lamBar lamHat muHat α W) (limS muBar γ W) τ PsiLim Q₁ A₁ →
      IsDiffusionSolution P' (limX lamBar lamHat muHat α W) (limS muBar γ W) τ PsiLim Q₂ A₂ →
      ∀ᵐ ω ∂P', ∀ t, 0 ≤ t → Q₁ ω t = Q₂ ω t ∧ A₁ ω t = A₂ ω t) ∧
    (∀ Qh Ah : Ω' → Path K,
      IsDiffusionSolution P' (limX lamBar lamHat muHat α W) (limS muBar γ W) τ PsiLim Qh Ah →
      CouplingConverges P P'
        (fun n ω t => Fin.append (Qhat n (Q n) ω t) (Ahat n (mu n) (A n) ω t))
        (fun ω t => Fin.append (Qh ω t) (Ah ω t))) := by sorry

end JSEQDelay.Diffusion
