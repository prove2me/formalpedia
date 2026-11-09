-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_proposition_A_2
-- name    : MinimaxAltRegret.Main.proposition_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:29.400492+00:00
-- url     : https://prove2.me/theorems/c7571bbf-7476-4eeb-9a76-8c962eb49df4
-- title:
--   Proposition A.2 — both derivatives and the curvature bound
-- statement:
--   Let d>=1, alpha>0, eta>0, and let R,ell,z be real d-vectors with ell and ell-z in [-1,1]^d. Put R(theta)=R-theta z, ell(theta)=ell-theta z, q_theta=q[eta R(theta)], and G_alpha(theta)=F(R(theta))-alpha eta Var_(q_theta)(ell(theta)). Write E_theta for expectation under q_theta, b=z-E_theta z and a=ell(theta)-E_theta ell(theta). For every theta in [0,1],
--
--   $$G'_\alpha(\theta)=-E_\theta z+2\alpha\eta E_\theta[ba]+\alpha\eta^2E_\theta[ba^2],$$
--
--   $$G''_\alpha(\theta)=(1-2\alpha)\eta E_\theta[b^2]-4\alpha\eta^2E_\theta[b^2a]-\alpha\eta^3E_\theta[b^2a^2]+\alpha\eta^3E_\theta[b^2]E_\theta[a^2]+2\alpha\eta^3(E_\theta[ba])^2,$$
--
--   $$G''_\alpha(\theta)\le[(1-2\alpha)\eta+8\alpha\eta^2+3\alpha\eta^3]\operatorname{Var}_{q_\theta}(z).$$
--
--   These are equations (21), (22), and (23), including every coefficient. They supply the calculation for the finite corrected potential and its continuous counterpart. There is no restriction z in [-1,1]^d.
--
--   Differences from the source:
--   - encoding: derivative equalities for the smooth interpolation, including its endpoints → HasDerivAt for G and its derivative at each theta in [0,1], together with the stated second-derivative inequality; reason: HasDerivAt asserts the full ordinary derivative of the same real extension and prevents a default derivative on a nondifferentiable input
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 14 / PDF p. 15, Proposition A.2, Eqs. (21)--(23); SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Experts

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem proposition_A_2 (d : ℕ) (hd : 0 < d) (α η : ℝ) (hα : 0 < α) (hη : 0 < η)
    (R ℓ z : ExpertVector d) (hℓ : ∀ i, ℓ i ∈ Set.Icc (-1 : ℝ) 1)
    (hend : ∀ i, ℓ i - z i ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      let q := expertEW η (fun i => R i - θ*z i)
      let a := expertCentered q (fun i => ℓ i - θ*z i)
      let b := expertCentered q z
      HasDerivAt (expertG α η R ℓ z)
        (-expertMean q z + 2*α*η*expertMean q (fun i => b i*a i) +
          α*η^2*expertMean q (fun i => b i*a i^2)) θ ∧
      HasDerivAt (deriv (expertG α η R ℓ z))
        ((1-2*α)*η*expertMean q (fun i => b i^2) -
          4*α*η^2*expertMean q (fun i => b i^2*a i) -
          α*η^3*expertMean q (fun i => b i^2*a i^2) +
          α*η^3*expertMean q (fun i => b i^2)*expertMean q (fun i => a i^2) +
          2*α*η^3*(expertMean q (fun i => b i*a i))^2) θ ∧
      deriv (deriv (expertG α η R ℓ z)) θ ≤
        ((1-2*α)*η + 8*α*η^2 + 3*α*η^3)*expertVariance q z := by sorry

end MinimaxAltRegret.Main
