-- Prove2me | Theorems.Thm_InteractionElim_Main_proposition_D_2
-- name    : InteractionElim.Main.proposition_D_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:21:54.826568+00:00
-- url     : https://prove2.me/theorems/fd48cbdc-d446-4e7c-8eaa-3a444331a675
-- title:
--   Proposition D.2 — an initial-teaching protocol of pointwise risk $\le\delta$ and fee $\le C\gamma\sum_jF(W_j)$
-- statement:
--   There is a universal constant $C>0$ such that, for every workflow instance in the regime (2.8), there is an initial-teaching protocol of pointwise whole-chain risk at most $\delta$ and worst-world expected fee at most
--   $$
--   C\gamma\sum_jF(W_j).
--   $$
--   With Proposition B.4 this proves (3.1).
--
--   **Formalization Note** The protocol is reliable, admissible and initial-teaching, i.e. a member of the class of $C_{pre}$.
--
--   Differences from the source:
--   - encoding: coordinates [R] = {1,…,R}, ordered blocks B_1,…,B_m, x ∈ F_2^R → `Fin R`, a surjective block map `Fin R → Fin m` (0-based stage order), vectors `Fin R → ZMod 2`; reason: index shift only; every ordered partition into nonempty blocks is such a surjection
--   - reading: §2 (p. 4) describes protocols in prose: a public parser, an expert whose bits depend only on Ax, the public history and its tape, an agent with private current-block queries that may preempt the expert by a submission, private abandonment, independent private tapes → `Protocol`/`step`/`run`: deterministic strategies of fair-coin tapes and views; the expert's abandonment is decided at every newly reached public history; an illegal move (query outside the current block, a paid bit out of turn, yielding when the expert is not designated) is abandonment; strategies are measurable in their tapes; reason: the source gives the model only in prose; this reading keeps every constraint of p. 4 (no shared tape, no free symbol, no clock), fair-coin tapes simulate any private randomization, and measurability is the standing convention that makes the execution law defined
--   - encoding: the fee (2.1) and the values C_ad, C_pre, C_lin as infima of fees → fees, C_ad, C_pre, C_lin in ℝ≥0∞ (lower integral of the path cost, supremum over worlds, infimum over the class); reason: (2.2)'s remark allows infinite-fee protocols; every finite value is the same real number
--   - encoding: universal constants, O(·) and ≍ → explicit existentially quantified positive real constants, quantified before every instance-dependent object; reason: the notation convention of p. 4: a ≍ b means two inequalities with positive universal constants
--   - reading: C_pre restricts discussion to one initial phase before any tool call or submission, ending at a parser leaf or phase flag fixed by its paid transcript → `InitialTeaching`: the parser's phase flag, once off, stays off and admits no paid-bit speaker; while it is on the agent neither queries nor submits; reason: the structural form of Definition 2.1 and the parsing paragraph of p. 4
--   - reading: the standing assumption (2.8) of all protocol-fee results ('Unless a statement explicitly specifies otherwise', p. 5) → hypothesis `I.Regime`; reason: the statement does not specify otherwise, so (2.8) applies
--   - reading: 'an initial-teaching protocol of pointwise whole-chain risk at most δ' → InitialTeaching ∧ Reliable ∧ Admissible; reason: 'Propositions B.4 and D.2 prove (3.1)' (p. 40), so the protocol is in the admissible class of C_pre
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 39, Proposition D.2

import Mathlib
import Definitions.Def_InteractionElim_Main_Protocol

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem proposition_D_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Instance, I.Regime →
      ∃ pr : Protocol I, InitialTeaching pr ∧ Reliable pr ∧ Admissible pr ∧
        fee pr ≤ ENNReal.ofReal (C * I.γ * I.Φ) := by sorry

end InteractionElim.Main
