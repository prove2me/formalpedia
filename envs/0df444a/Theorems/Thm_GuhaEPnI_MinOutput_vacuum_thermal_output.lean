-- Prove2me | Theorems.Thm_GuhaEPnI_MinOutput_vacuum_thermal_output
-- name    : GuhaEPnI.MinOutput.vacuum_thermal_output
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:02.999993+00:00
-- url     : https://prove2.me/theorems/e40225c1-8aef-4e1f-b855-3206c76d47b5
-- title:
--   §III, p. 3 — vacuum and thermal inputs yield a thermal output
-- statement:
--   Take transmissivity $\eta\in[0,1]$, thermal mean $K\ge0$, an $n$-mode vacuum at the first beam-splitter input, and an $n$-mode thermal product state of mean $K$ at the second. An output state exists; every state satisfying the beam-splitter output relation is thermal with mean $(1-\eta)K$ in each mode:
--
--   $$\rho_c=\rho_T^{\otimes n}((1-\eta)K).$$
--
--   This supplies the attained output in both minimum entropy conjectures.
-- source:
--   Guha, Erkmen & Shapiro, The Entropy Photon-Number Inequality and its Consequences, arXiv:0710.5666v2, p. 3, §III, proof of Conjecture 1 after Eq. (16)

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_GuhaEPnI_MinOutput_States

namespace GuhaEPnI.MinOutput
open OAI.EntropyPhotonNumber

theorem vacuum_thermal_output (n : ℕ) (η K : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hK : 0 ≤ K) (ρA ρB : State n) (hA : IsVacuum ρA)
    (hB : IsThermal K ρB) :
    (∃ ρC : State n, IsBeamSplitterOutput η ρA ρB ρC) ∧
    (∀ ρC : State n, IsBeamSplitterOutput η ρA ρB ρC →
      IsThermal ((1 - η) * K) ρC) := by sorry

end GuhaEPnI.MinOutput
