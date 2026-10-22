-- Prove2me | Theorems.Thm_GuhaEPnI_MinOutput_thermal_exists
-- name    : GuhaEPnI.MinOutput.thermal_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:52.730265+00:00
-- url     : https://prove2.me/theorems/96b8ae29-306a-43bb-91d0-3b14fa112b1b
-- title:
--   Eq. (10), p. 2 — thermal photon-number weights define a state
-- statement:
--   For every number $n$ of modes and every mean photon number $N\ge 0$, an $n$-mode density operator exists whose number-basis matrix is the product of the thermal weights $N^m/(N+1)^{m+1}$ over the modes:
--
--   $$\langle k|\rho_T|l\rangle=\mathbf 1_{k=l}\prod_{j=1}^{n}\frac{N^{k_j}}{(N+1)^{k_j+1}}.$$
--
--   Existence ensures that optimization over thermal inputs includes an actual density operator, including at $N=0$.
-- source:
--   Guha, Erkmen & Shapiro, The Entropy Photon-Number Inequality and its Consequences, arXiv:0710.5666v2, p. 2, Eq. (10)

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_GuhaEPnI_MinOutput_States

namespace GuhaEPnI.MinOutput
open OAI.EntropyPhotonNumber

theorem thermal_exists (n : ℕ) :
    ∀ N : ℝ, 0 ≤ N → ∃ ρ : State n, IsThermal N ρ := by sorry

end GuhaEPnI.MinOutput
