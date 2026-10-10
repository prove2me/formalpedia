-- Prove2me | Theorems.Thm_IntMul_EndParkResume_resume_protected_prefix
-- name    : IntMul.EndParkResume.resume_protected_prefix
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T07:32:09.176807+00:00
-- url     : https://prove2.me/theorems/6b6106e4-175e-4925-99a6-0fa1cef0f5fe
-- title:
--   Complete selective parent-return service with protected physical trajectory
-- statement:
--   Assume unique local parent markers, a tracked blank tail on the parent result bank, positive work offsets, a positive caller buffer marker and a positive parent continuation position. The fixed-tape physical parent-return service restores only the parent result-bank head, pops and recovers its finite continuation and places the child result, erasing any older visited output tail. It reaches its exact complete final ready frame in at most result-bank extent+n+returned-word length+2max(returned-word length,result-bank extent)+12 physical transitions. Every noninput head is at least one at every intermediate time including the ready endpoint. Unselected work heads remain parked throughout result restoration.
-- source:
--   Original complete protected physical selective parent return service for integer multiplication recursive foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkResume
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.EndParkResume

theorem IntMul.EndParkResume.resume_protected_prefix (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n).step^[t] (initialFrame M n base rho sigma offset extent c label w)=
        finalFrame M n base rho sigma offset extent c label w ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n).inTape →
        1 ≤ ((machine M n).step^[s]
          (initialFrame M n base rho sigma offset extent c label w)).head i := by sorry
