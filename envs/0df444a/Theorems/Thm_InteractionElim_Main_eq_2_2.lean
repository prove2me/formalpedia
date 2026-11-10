-- Prove2me | Theorems.Thm_InteractionElim_Main_eq_2_2
-- name    : InteractionElim.Main.eq_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:21:44.447992+00:00
-- url     : https://prove2.me/theorems/0012f330-a137-44dd-9e10-12ca30eda0c2
-- title:
--   §2, Eq. (2.2) — the protocol inclusions $C_{ad}\le C_{pre}\le C_{lin}$
-- statement:
--   For every workflow instance, the optimal fee over all reliable admissible protocols, over reliable admissible initial-teaching protocols, and over reliable admissible fixed-linear-teaching protocols are ordered:
--   $$
--   C_{ad}\le C_{pre}\le C_{lin}.
--   $$
--   Each class contains the next, so the infima are ordered; the inequalities place initial teaching between unrestricted ongoing interaction and fixed linear lessons.
--
--   Differences from the source:
--   - encoding: coordinates [R] = {1,…,R}, ordered blocks B_1,…,B_m, x ∈ F_2^R → `Fin R`, a surjective block map `Fin R → Fin m` (0-based stage order), vectors `Fin R → ZMod 2`; reason: index shift only; every ordered partition into nonempty blocks is such a surjection
--   - reading: §2 (p. 4) describes protocols in prose: a public parser, an expert whose bits depend only on Ax, the public history and its tape, an agent with private current-block queries that may preempt the expert by a submission, private abandonment, independent private tapes → `Protocol`/`step`/`run`: deterministic strategies of fair-coin tapes and views; the expert's abandonment is decided at every newly reached public history; an illegal move (query outside the current block, a paid bit out of turn, yielding when the expert is not designated) is abandonment; strategies are measurable in their tapes; reason: the source gives the model only in prose; this reading keeps every constraint of p. 4 (no shared tape, no free symbol, no clock), fair-coin tapes simulate any private randomization, and measurability is the standing convention that makes the execution law defined
--   - encoding: the fee (2.1) and the values C_ad, C_pre, C_lin as infima of fees → fees, C_ad, C_pre, C_lin in ℝ≥0∞ (lower integral of the path cost, supremum over worlds, infimum over the class); reason: (2.2)'s remark allows infinite-fee protocols; every finite value is the same real number
--   - reading: C_pre restricts discussion to one initial phase before any tool call or submission, ending at a parser leaf or phase flag fixed by its paid transcript → `InitialTeaching`: the parser's phase flag, once off, stays off and admits no paid-bit speaker; while it is on the agent neither queries nor submits; reason: the structural form of Definition 2.1 and the parsing paragraph of p. 4
--   - reading: C_lin restricts teaching to a basis of Sx for a public fixed S with row S ⊆ row A; bit values use only Sx, public data and the original tapes; any lossless recoding must recover the labels; expert abandonment may depend on Ax → `LinearTeaching`: initial teaching with S = M·A, expert bits depending on the record only through Sx, and a decoder recovering Sx from the paid transcript, the agent's original tape and u whenever the initial phase has ended without failure; expert abandonment unrestricted; reason: Definition 2.1 (p. 4) requires lossless label recovery; Appendix E (pp. 40-41, (E.4)) counts normally completed leaves and excludes premature abandonment. A decoder uses only information the agent actually has
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 5, §2, Eq. (2.2)

import Mathlib
import Definitions.Def_InteractionElim_Main_Protocol

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem eq_2_2 (I : Instance) : Cad I ≤ Cpre I ∧ Cpre I ≤ Clin I := by sorry

end InteractionElim.Main
