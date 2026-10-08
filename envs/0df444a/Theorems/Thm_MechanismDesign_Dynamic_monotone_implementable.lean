-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_monotone_implementable
-- name    : MechanismDesign.Dynamic.monotone_implementable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T05:53:59.323898+00:00
-- url     : https://prove2.me/theorems/656e49df-892d-4359-87a2-40497888bad9
-- title:
--   Proposition 11.6 -- allocation rules increasing in $\tau$ and $\theta$ are implementable
-- statement:
--   Let $q:[\underline\tau,\bar\tau]\times[\underline\theta,\bar\theta]\to[0,1]$ be measurable and increasing in $\tau$ and in $\theta$. Then there exists a (measurable) transfer schedule $t(\tau,\theta)$ such that the direct mechanism $(q,t)$ is incentive-compatible in the sequential screening model.
--
--   Incentive compatibility does not force $q$ to be increasing in $\tau$; this result shows that monotonicity in both arguments is nevertheless sufficient, thanks to first-order stochastic dominance. It is what makes the candidate optimal allocation rule implementable.
--
--   **Formalization Note** Measurability of $q$ is the measurability the book omits; the transfer schedule is asserted to be measurable as well.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.215, Proposition 11.6

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.6**, p.215. If `q(τ, θ)` (with values in `[0, 1]`, measurable) is
increasing in `τ` and in `θ`, then there exists a (measurable) transfer schedule `t(τ, θ)` such
that the direct mechanism `(q, t)` is incentive-compatible. -/
theorem monotone_implementable {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (q : ℝ → ℝ → ℝ)
    (hq : ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi, q τ θ ∈ Set.Icc (0 : ℝ) 1)
    (hqm : Measurable (fun p : Set.Icc τlo τhi × Set.Icc θlo θhi => q p.1 p.2))
    (hτ : ∀ θ ∈ Set.Icc θlo θhi, MonotoneOn (fun τ => q τ θ) (Set.Icc τlo τhi))
    (hθ : ∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (q τ) (Set.Icc θlo θhi)) :
    ∃ t : ℝ → ℝ → ℝ, (⟨q, t⟩ : DirectMechanism τlo τhi θlo θhi).Admissible ∧
      (⟨q, t⟩ : DirectMechanism τlo τhi θlo θhi).IsIC E := by sorry

end MechanismDesign.Dynamic
