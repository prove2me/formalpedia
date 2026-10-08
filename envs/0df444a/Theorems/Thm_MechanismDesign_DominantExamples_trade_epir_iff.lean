-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_trade_epir_iff
-- name    : MechanismDesign.DominantExamples.trade_epir_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:46:19.750636+00:00
-- url     : https://prove2.me/theorems/f588cf01-fc41-4445-bf39-9b3d8f7bca7a
-- title:
--   Proposition 4.10 — ex post IR in bilateral trade binds at the highest seller type and the lowest buyer type
-- statement:
--   Let $(q, t_S, t_B)$ be a dominant strategy incentive-compatible deterministic direct bilateral trade mechanism on $\Theta = [\underline\theta_S,\bar\theta_S]\times[\underline\theta_B,\bar\theta_B]$. It is ex post individually rational if and only if
--   $$t_S(\bar\theta_S,\theta_B) \ge \bar\theta_S\, q(\bar\theta_S,\theta_B) \quad\text{for every } \theta_B \in [\underline\theta_B,\bar\theta_B],$$
--   and
--   $$t_B(\theta_S,\underline\theta_B) \le \underline\theta_B\, q(\theta_S,\underline\theta_B) \quad\text{for every } \theta_S \in [\underline\theta_S,\bar\theta_S].$$
--
--   The seller's participation constraint needs to be checked only at her highest type, the buyer's only at his lowest type.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.91, Proposition 4.10

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade

namespace MechanismDesign.DominantExamples

/-- Proposition 4.10, p.91. A dominant strategy incentive-compatible direct bilateral trade
mechanism is ex post individually rational if and only if for every `θ_B ∈ [θ̲_B, θ̄_B]`,
`t_S(θ̄_S, θ_B) ≥ θ̄_S q(θ̄_S, θ_B)`, and for every `θ_S ∈ [θ̲_S, θ̄_S]`,
`t_B(θ_S, θ̲_B) ≤ θ̲_B q(θ_S, θ̲_B)`. -/
theorem trade_epir_iff {E : TradeSetting} (M : TradeMechanism E) (hM : M.IsDSIC) :
    M.IsEPIR ↔
      (∀ θB ∈ Set.Icc E.loB E.hiB, E.hiS * M.q (E.hiS, θB) ≤ M.tS (E.hiS, θB)) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, M.tB (θS, E.loB) ≤ E.loB * M.q (θS, E.loB)) := by sorry

end MechanismDesign.DominantExamples
