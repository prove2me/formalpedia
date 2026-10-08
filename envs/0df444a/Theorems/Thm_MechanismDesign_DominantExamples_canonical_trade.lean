-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_canonical_trade
-- name    : MechanismDesign.DominantExamples.canonical_trade
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:30:55.820857+00:00
-- url     : https://prove2.me/theorems/08ce6bf5-b4cf-448f-9b5d-29cc887028eb
-- title:
--   Proposition 4.11 — canonical trading mechanisms are dominant strategy IC and ex post IR
-- statement:
--   Let $(q, t_S, t_B)$ be a canonical bilateral trade mechanism (Definition 4.5): for strictly increasing continuous $\psi_S, \psi_B$, trade takes place iff $\psi_B(\theta_B) \ge \psi_S(\theta_S)$; the seller then receives the largest type with which she would still have traded, and the buyer pays the smallest type with which he would still have traded. Then the mechanism is dominant strategy incentive-compatible and ex post individually rational. Moreover,
--   $$u_S(\bar\theta_S,\theta_B) = \bar\theta_S \ \text{ for every } \theta_B \in [\underline\theta_B,\bar\theta_B], \qquad u_B(\theta_S,\underline\theta_B) = 0 \ \text{ for every } \theta_S \in [\underline\theta_S,\bar\theta_S],$$
--   where $u_S(\theta) = \theta_S(1 - q(\theta)) + t_S(\theta)$ and $u_B(\theta) = \theta_B q(\theta) - t_B(\theta)$.
--
--   Canonical mechanisms need not balance the budget: the seller may receive more than the buyer pays.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.92, Proposition 4.11

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade

namespace MechanismDesign.DominantExamples

/-- Proposition 4.11, p.92. Every canonical bilateral trade mechanism is dominant strategy
incentive-compatible and ex post individually rational. Moreover, `u_S(θ̄_S, θ_B) = θ̄_S` for
every `θ_B ∈ [θ̲_B, θ̄_B]` and `u_B(θ_S, θ̲_B) = 0` for every `θ_S ∈ [θ̲_S, θ̄_S]`. -/
theorem canonical_trade {E : TradeSetting} (M : TradeMechanism E) (hM : M.IsCanonical) :
    M.IsDSIC ∧ M.IsEPIR ∧
      (∀ θB ∈ Set.Icc E.loB E.hiB, M.uS (E.hiS, θB) = E.hiS) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, M.uB (θS, E.loB) = 0) := by sorry

end MechanismDesign.DominantExamples
