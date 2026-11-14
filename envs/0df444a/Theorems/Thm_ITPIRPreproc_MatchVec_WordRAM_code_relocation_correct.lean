-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_WordRAM_code_relocation_correct
-- name    : ITPIRPreproc.MatchVec.WordRAM.code_relocation_correct
-- status  : Proved
-- author  : @Jesko
-- created : 2026-11-13T17:56:09.871628+00:00
-- url     : https://prove2.me/theorems/1815f3e7-ef95-4897-a5f9-82f95a035b8a
-- title:
--   Word-RAM code relocation preserves execution and exact costs
-- statement:
--   Let $A$ and $P$ be arbitrary finite word-RAM programs, and let $b=|A|$. Place $P$ after $A$, adding $b$ to every absolute jump target in $P$. For any initial state $s$, input, coin tape, and number of steps $k$, execution of the relocated block from the state with program counter $b+s.\mathrm{pc}$ equals the original execution with its final program counter shifted by $b$:
--   $$\operatorname{step}_{A\mathbin{\|}\operatorname{reloc}_b(P)}^k(\operatorname{shift}_b(s))
--   =\operatorname{shift}_b(\operatorname{step}_P^k(s)).$$
--   All other state fields, including accumulated work, agree exactly; hence storage at corresponding states also agrees. The combined program is deterministic exactly when both constituent programs are deterministic, and is streaming exactly when both constituents are streaming.
--
--   This lemma permits a verified code block to be placed at an arbitrary address without changing its behavior or cost. Execution starts inside the relocated block; the statement does not claim that the preceding code has been executed or that arbitrary blocks can be sequentially composed without an interface invariant.
-- source:
--   Derived implementation lemma for Definitions.Def_ITPIRPreproc_MatchVec_Machine and Definitions.Def_ITPIRPreproc_MatchVec_RAMRelocation. Used as program-construction infrastructure for the Dujmovic-Lai-Wichs PIR formalization; the lemma is supplied by this formalization rather than stated in the paper.

import Definitions.Def_ITPIRPreproc_MatchVec_RAMRelocation
import Mathlib.Tactic
open ITPIRPreproc.MatchVec.WordRAM

theorem ITPIRPreproc.MatchVec.WordRAM.code_relocation_correct (precode P : Program) :
    (Deterministic (placeAfter precode P) ↔ Deterministic precode ∧ Deterministic P) ∧
    (Streaming (placeAfter precode P) ↔ Streaming precode ∧ Streaming P) ∧
    ∀ (inp : List Bool) (ω : ℕ → Bool) (s : State) (k : ℕ),
      (step (placeAfter precode P) inp ω)^[k] (relocateState precode.length s) =
        relocateState precode.length ((step P inp ω)^[k] s) := by sorry
