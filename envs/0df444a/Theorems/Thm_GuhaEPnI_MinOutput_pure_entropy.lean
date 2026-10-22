-- Prove2me | Theorems.Thm_GuhaEPnI_MinOutput_pure_entropy
-- name    : GuhaEPnI.MinOutput.pure_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:00.200662+00:00
-- url     : https://prove2.me/theorems/1a55e036-ee5d-48d4-b115-184692ca0d22
-- title:
--   §III, p. 3 — a pure state has zero von Neumann entropy
-- statement:
--   If an $n$-mode density operator is the projector onto a unit Fock vector, then its von Neumann entropy is zero:
--
--   $$S(\rho)=0.$$
--
--   This supplies the pure-input entropy used in Eqs. (16) and (17).
-- source:
--   Guha, Erkmen & Shapiro, The Entropy Photon-Number Inequality and its Consequences, arXiv:0710.5666v2, p. 3, §III, proof of Conjecture 1 before Eq. (16)

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_GuhaEPnI_MinOutput_States

namespace GuhaEPnI.MinOutput
open OAI.EntropyPhotonNumber

theorem pure_entropy (n : ℕ) (ρ : State n) (hρ : IsPure ρ) :
    entropy ρ = 0 := by sorry

end GuhaEPnI.MinOutput
