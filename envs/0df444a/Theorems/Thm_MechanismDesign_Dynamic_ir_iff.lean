-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_ir_iff
-- name    : MechanismDesign.Dynamic.ir_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T05:54:10.545634+00:00
-- url     : https://prove2.me/theorems/4cfbe43f-e856-4860-9211-ed2a2c77f04c
-- title:
--   Proposition 11.7 -- individual rationality reduces to $U(\underline\tau)\ge0$
-- statement:
--   An admissible, incentive-compatible direct mechanism in the sequential screening model is individually rational (that is, $U(\tau)\ge0$ for all $\tau\in[\underline\tau,\bar\tau]$) if and only if
--   $$U(\underline\tau)\ge0 .$$
--
--   Only the participation constraint of the lowest ex ante type needs to be checked; the seller's revenue problem then sets $U(\underline\tau)=0$.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.216, Proposition 11.7

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.7**, p.216. An (admissible) incentive-compatible direct mechanism is
individually rational if and only if `U(τ̲) ≥ 0`. -/
theorem ir_iff {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    m.IsIR E ↔ 0 ≤ m.U E τlo := by sorry

end MechanismDesign.Dynamic
