-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_ic_iff
-- name    : MechanismDesign.Dynamic.ic_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T05:53:39.826983+00:00
-- url     : https://prove2.me/theorems/953c8bcd-a42c-4088-840c-e07cbfa43b75
-- title:
--   Proposition 11.2 -- incentive compatibility reduces to (11.1) and (11.2)
-- statement:
--   Consider an admissible direct mechanism $(q,t)$ in the sequential screening model. It is incentive-compatible (Definition 11.2) if and only if it satisfies (11.1), $u(\tau,\theta)\ge\theta q(\tau,\theta')-t(\tau,\theta')$ for all $\tau,\theta,\theta'$, and
--   $$U(\tau)\ge\hat U(\tau'\mid\tau)\qquad\text{for all }\tau,\tau'\in[\underline\tau,\bar\tau].\qquad(11.2)$$
--
--   The result removes the reporting functions from Definition 11.2(ii): after a lie about her ex ante type the buyer still reports her ex post type truthfully, because her ex post type is her payoff type.
--
--   **Formalization Note** Admissibility (measurability of $q$, $t$ and $q\in[0,1]$) makes the integrals of Definition 11.2(ii) well defined; reporting functions are measurable.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.209, Proposition 11.2, Eq. (11.2)

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.2**, p.209. An (admissible) direct mechanism is incentive-compatible if and
only if it satisfies (11.1) and (11.2): `U(τ) ≥ Û(τ′|τ)` for all `τ, τ′ ∈ [τ̲, τ̄]`. -/
theorem ic_iff {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) :
    m.IsIC E ↔ m.IsExPostIC ∧
      ∀ τ ∈ Set.Icc τlo τhi, ∀ τ' ∈ Set.Icc τlo τhi, m.Uhat E τ' τ ≤ m.U E τ := by sorry

end MechanismDesign.Dynamic
