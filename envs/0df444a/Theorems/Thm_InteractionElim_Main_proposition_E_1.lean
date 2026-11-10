-- Prove2me | Theorems.Thm_InteractionElim_Main_proposition_E_1
-- name    : InteractionElim.Main.proposition_E_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:21:41.213421+00:00
-- url     : https://prove2.me/theorems/4a918f94-ae4a-4641-bcb9-efc68fcccec0
-- title:
--   Proposition E.1 — the fixed-linear teaching value satisfies (3.2)
-- statement:
--   There are universal constants $c,C>0$ such that, for every workflow instance in the regime (2.8),
--   $$
--   c\gamma\sum_jG(W_j)\le C_{lin}\le C\gamma\sum_jG(W_j). \tag{3.2}
--   $$
--   Linear lessons leave affine cells, so the functional $G$ replaces $F$.
--
--   Differences from the source:
--   - encoding: coordinates [R] = {1,…,R}, ordered blocks B_1,…,B_m, x ∈ F_2^R → `Fin R`, a surjective block map `Fin R → Fin m` (0-based stage order), vectors `Fin R → ZMod 2`; reason: index shift only; every ordered partition into nonempty blocks is such a surjection
--   - reading: §2 (p. 4) describes protocols in prose: a public parser, an expert whose bits depend only on Ax, the public history and its tape, an agent with private current-block queries that may preempt the expert by a submission, private abandonment, independent private tapes → `Protocol`/`step`/`run`: deterministic strategies of fair-coin tapes and views; the expert's abandonment is decided at every newly reached public history; an illegal move (query outside the current block, a paid bit out of turn, yielding when the expert is not designated) is abandonment; strategies are measurable in their tapes; reason: the source gives the model only in prose; this reading keeps every constraint of p. 4 (no shared tape, no free symbol, no clock), fair-coin tapes simulate any private randomization, and measurability is the standing convention that makes the execution law defined
--   - encoding: the fee (2.1) and the values C_ad, C_pre, C_lin as infima of fees → fees, C_ad, C_pre, C_lin in ℝ≥0∞ (lower integral of the path cost, supremum over worlds, infimum over the class); reason: (2.2)'s remark allows infinite-fee protocols; every finite value is the same real number
--   - encoding: universal constants, O(·) and ≍ → explicit existentially quantified positive real constants, quantified before every instance-dependent object; reason: the notation convention of p. 4: a ≍ b means two inequalities with positive universal constants
--   - reading: C_lin restricts teaching to a basis of Sx for a public fixed S with row S ⊆ row A; bit values use only Sx, public data and the original tapes; any lossless recoding must recover the labels; expert abandonment may depend on Ax → `LinearTeaching`: initial teaching with S = M·A, expert bits depending on the record only through Sx, and a decoder recovering Sx from the paid transcript, the agent's original tape and u whenever the initial phase has ended without failure; expert abandonment unrestricted; reason: Definition 2.1 (p. 4) requires lossless label recovery; Appendix E (pp. 40-41, (E.4)) counts normally completed leaves and excludes premature abandonment. A decoder uses only information the agent actually has
--   - reading: the standing assumption (2.8) of all protocol-fee results ('Unless a statement explicitly specifies otherwise', p. 5) → hypothesis `I.Regime`; reason: the statement does not specify otherwise, so (2.8) applies
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 40, Proposition E.1

import Mathlib
import Definitions.Def_InteractionElim_Main_Protocol

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem proposition_E_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ I : Instance, I.Regime →
      ENNReal.ofReal (c * I.γ * I.sumG) ≤ Clin I ∧
        Clin I ≤ ENNReal.ofReal (C * I.γ * I.sumG) := by sorry

end InteractionElim.Main
