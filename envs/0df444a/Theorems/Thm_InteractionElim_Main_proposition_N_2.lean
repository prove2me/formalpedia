-- Prove2me | Theorems.Thm_InteractionElim_Main_proposition_N_2
-- name    : InteractionElim.Main.proposition_N_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:23:12.984071+00:00
-- url     : https://prove2.me/theorems/7c8c53d3-c0a0-4bab-bc47-e202a1b23892
-- title:
--   Proposition N.2 — both initial upper bounds in time $2^{O(2^k)}\mathrm{poly}(N,L)$; the nonlinear one with call cap $O(RL\log(RL)\log R)$
-- statement:
--   Both initial upper bounds in Theorem 3.1 can be constructed and executed in time $2^{O(2^k)}\mathrm{poly}(N,L)$, and the nonlinear upper bound has a deterministic call cap $O(RL\log(RL)\log R)$. Formally, there are a universal constant $C>0$ and two programs of the bit-cost machine such that for every workflow instance in the regime (2.8):
--
--   1. the protocol induced by the first is reliable, admissible, initial-teaching, has fee at most $C\gamma\sum_jF(W_j)$, runs in at most $C\,2^{C2^k}(N+L+2)^C$ machine steps on every path, and makes at most $C\,RL\ln(RL)\ln R$ calls on every path;
--   2. the protocol induced by the second is reliable, admissible, fixed-linear, has fee at most $C\gamma\sum_jG(W_j)$, and runs in at most $C\,2^{C2^k}(N+L+2)^C$ machine steps on every path.
--
--   Construction (the geometric optimization over cells) and decoding are included in the time.
--
--   Differences from the source:
--   - encoding: coordinates [R] = {1,…,R}, ordered blocks B_1,…,B_m, x ∈ F_2^R → `Fin R`, a surjective block map `Fin R → Fin m` (0-based stage order), vectors `Fin R → ZMod 2`; reason: index shift only; every ordered partition into nonempty blocks is such a surjection
--   - reading: §2 (p. 4) describes protocols in prose: a public parser, an expert whose bits depend only on Ax, the public history and its tape, an agent with private current-block queries that may preempt the expert by a submission, private abandonment, independent private tapes → `Protocol`/`step`/`run`: deterministic strategies of fair-coin tapes and views; the expert's abandonment is decided at every newly reached public history; an illegal move (query outside the current block, a paid bit out of turn, yielding when the expert is not designated) is abandonment; strategies are measurable in their tapes; reason: the source gives the model only in prose; this reading keeps every constraint of p. 4 (no shared tape, no free symbol, no clock), fair-coin tapes simulate any private randomization, and measurability is the standing convention that makes the execution law defined
--   - encoding: the fee (2.1) and the values C_ad, C_pre, C_lin as infima of fees → fees, C_ad, C_pre, C_lin in ℝ≥0∞ (lower integral of the path cost, supremum over worlds, infimum over the class); reason: (2.2)'s remark allows infinite-fee protocols; every finite value is the same real number
--   - encoding: universal constants, O(·) and ≍ → explicit existentially quantified positive real constants, quantified before every instance-dependent object; reason: the notation convention of p. 4: a ≍ b means two inequalities with positive universal constants
--   - reading: C_pre restricts discussion to one initial phase before any tool call or submission, ending at a parser leaf or phase flag fixed by its paid transcript → `InitialTeaching`: the parser's phase flag, once off, stays off and admits no paid-bit speaker; while it is on the agent neither queries nor submits; reason: the structural form of Definition 2.1 and the parsing paragraph of p. 4
--   - reading: C_lin restricts teaching to a basis of Sx for a public fixed S with row S ⊆ row A; bit values use only Sx, public data and the original tapes; any lossless recoding must recover the labels; expert abandonment may depend on Ax → `LinearTeaching`: initial teaching with S = M·A, expert bits depending on the record only through Sx, and a decoder recovering Sx from the paid transcript, the agent's original tape and u whenever the initial phase has ended without failure; expert abandonment unrestricted; reason: Definition 2.1 (p. 4) requires lossless label recovery; Appendix E (pp. 40-41, (E.4)) counts normally completed leaves and excludes premature abandonment. A decoder uses only information the agent actually has
--   - reading: a uniform implementation in time 2^{O(2^k)} poly(N, L), including construction and decoding → one program of the mission's bit-cost stack machine, fixed before the instance, whose parser, agent and expert decisions are halting runs on the explicit input and the deciding party's view; `implTime` (all machine steps, including both parser speaker and phase computations, of all decisions along a path) ≤ C·2^{C·2^k}·(N+L+2)^C on every path of every world; reason: the source names no machine; replay of a stateful bit algorithm from its input, tape and observation log has polynomial overhead in its total time. A polynomial in 2^{O(2^k)}poly(N,L) has the same form, so recomputing construction and decoding preserves the asserted bound
--   - reading: at most O(RL log(RL) log R) actual tool calls on every path → at every step of every execution path of every world the total number of calls is ≤ C·R·L·ln(R·L)·ln R; reason: 'on every path' is a deterministic cap; R ≥ 16 and L ≥ ln 17 make the right side ≥ 1, so no additive constant is lost
--   - reading: the standing assumption (2.8) of all protocol-fee results ('Unless a statement explicitly specifies otherwise', p. 5) → hypothesis `I.Regime`; reason: the statement does not specify otherwise, so (2.8) applies
--   - reading: 'Both initial upper bounds in Theorem 3.1' → the first program achieves the C_pre bound (fee ≤ CγΣF(W_j), initial teaching), the second the C_lin bound (fee ≤ CγΣG(W_j), fixed-linear teaching), each reliable and admissible; reason: the two upper bounds of (3.1) and (3.2)
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 95, Proposition N.2 (proof §F.7, pp. 47-48)

import Mathlib
import Definitions.Def_InteractionElim_Main_Machine

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem proposition_N_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ prog₁ prog₂ : Program, ∀ I : Instance, I.Regime →
      (Reliable (inducedProtocol prog₁ I) ∧ Admissible (inducedProtocol prog₁ I) ∧
        InitialTeaching (inducedProtocol prog₁ I) ∧
        fee (inducedProtocol prog₁ I) ≤ ENNReal.ofReal (C * I.γ * I.Φ) ∧
        (∀ x u ω, implTime prog₁ I x u ω ≤
          ENNReal.ofReal (C * (2 : ℝ) ^ (C * (2 : ℝ) ^ I.k) * ((I.N : ℝ) + I.L + 2) ^ C)) ∧
        (∀ x u ω t, ((run (inducedProtocol prog₁ I) x u ω t).totalCalls : ℝ) ≤
          C * I.R * I.L * Real.log ((I.R : ℝ) * I.L) * Real.log I.R)) ∧
      (Reliable (inducedProtocol prog₂ I) ∧ Admissible (inducedProtocol prog₂ I) ∧
        LinearTeaching (inducedProtocol prog₂ I) ∧
        fee (inducedProtocol prog₂ I) ≤ ENNReal.ofReal (C * I.γ * I.sumG) ∧
        (∀ x u ω, implTime prog₂ I x u ω ≤
          ENNReal.ofReal (C * (2 : ℝ) ^ (C * (2 : ℝ) ^ I.k) * ((I.N : ℝ) + I.L + 2) ^ C))) := by sorry

end InteractionElim.Main
