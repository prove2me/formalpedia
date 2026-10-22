-- Prove2me | Theorems.Thm_GuhaEPnI_MinOutput_thermal_entropy
-- name    : GuhaEPnI.MinOutput.thermal_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:55.384307+00:00
-- url     : https://prove2.me/theorems/042e207d-3bb5-4d16-ae1f-32bca6143ef6
-- title:
--   §II.B, p. 2 — entropy and finite energy of the thermal product state
-- statement:
--   Let $\rho_T$ be the product thermal state on $n$ modes, with mean photon number $N\ge 0$ in each mode. It has finite expected total photon number, and its von Neumann entropy is
--
--   $$S(\rho_T)=n\,g(N).$$
--
--   The one-mode identity appears after Eq. (10); the product form is used for the entropy values on p. 3.
-- source:
--   Guha, Erkmen & Shapiro, The Entropy Photon-Number Inequality and its Consequences, arXiv:0710.5666v2, p. 2, §II.B after Eq. (10); p. 3, proofs of Conjectures 1–2

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_GuhaEPnI_MinOutput_States

namespace GuhaEPnI.MinOutput
open OAI.EntropyPhotonNumber

theorem thermal_entropy (n : ℕ) (N : ℝ) (ρ : State n)
    (hN : 0 ≤ N) (hρ : IsThermal N ρ) :
    FiniteEnergy ρ ∧ entropy ρ = (n : ℝ) * g N := by sorry

end GuhaEPnI.MinOutput
