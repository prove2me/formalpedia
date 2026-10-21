-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_proposition_2_3
-- name    : JSEQDelay.Diffusion.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:56.84428+00:00
-- url     : https://prove2.me/theorems/1eaba3c3-6f62-4ae6-800e-c5dd70c38f1d
-- title:
--   Proposition 2.3, p. 9 — under heavy traffic, (X̂ⁿ, Ŝⁿ) converges in distribution to Brownian motions (X̂, Ŝ)
-- statement:
--   Assume the primitives of §2.1 and the heavy traffic condition (Assumption 2.2). Let $\hat X^n(t)=(X^n(t)-\langle\mu^n,\mathbf 1\rangle t)/\sqrt n$ and $\hat S^n_k(t)=(S^n_k(t)-\mu^n_kt)/\sqrt n$. Let $\hat X$ be a Brownian motion with drift $\hat\lambda-\langle\hat\mu,\mathbf 1\rangle$ and variance $\bar\lambda\alpha^2$ and $\hat S$ an independent $K$-dimensional driftless Brownian motion with covariance $\mathrm{diag}(\bar\mu_k\gamma_k^2)$. Then
--   $$(\hat X^n,\hat S^n)\Rightarrow(\hat X,\hat S)\qquad(n\to\infty)$$
--   jointly, in the Skorokhod space of $\mathbb R^{K+1}$-valued paths.
--
--   This is the functional central limit theorem for renewal processes in the heavy-traffic parametrization; it is the source of all randomness in the diffusion model.
--
--   **Formalization Note** Convergence in distribution to a continuous limit is the published coupling form `CouplingConverges`: on some probability space there are copies converging almost surely uniformly on compacts. The limit is built from a standard $(K+1)$-dimensional Brownian motion $W$ on an arbitrary probability space (any such space carries the page's $(\hat X,\hat S)$ in law).
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 9, Proposition 2.3 (with the definition of X̂, Ŝ just above it)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_JSEQDelay_Diffusion_Model
import Definitions.Def_JSEQDelay_Diffusion_DiffusionModel

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-- **Proposition 2.3** (p. 9): under the heavy traffic condition (Assumption 2.2), the
centred and scaled exogenous arrival and service processes `(X̂ⁿ, Ŝⁿ)` converge jointly in
distribution to `(X̂, Ŝ)`: a one-dimensional Brownian motion with drift `λ̂ − ⟨μ̂, 𝟏⟩` and variance
`λ̄ α²`, and an independent `K`-dimensional Brownian motion with zero drift and covariance
`diag(μ̄_k γ_k²)` (here built from a standard `(K + 1)`-dimensional Brownian motion `W` on
`(Ω', P')`). -/
theorem proposition_2_3 {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (α : ℝ) (γ : Fin K → ℝ)
    (hprim : Primitives P u v α γ)
    (lam : ℕ → ℝ) (mu : ℕ → Fin K → ℝ) (lamBar lamHat : ℝ) (muBar muHat : Fin K → ℝ)
    (hrates : Rates lam mu) (hHT : HeavyTraffic lam mu lamBar lamHat muBar muHat)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : Ω' → ℝ → Fin (K + 1) → ℝ) (hW : IsStandardBM P' W) :
    CouplingConverges P P'
      (fun n ω t => (Fin.cons (Xhat n u (lam n) (mu n) ω t) (Shat n v (mu n) ω t) :
        Fin (K + 1) → ℝ))
      (fun ω t => (Fin.cons (limX lamBar lamHat muHat α W ω t) (limS muBar γ W ω t) :
        Fin (K + 1) → ℝ)) := by sorry

end JSEQDelay.Diffusion
