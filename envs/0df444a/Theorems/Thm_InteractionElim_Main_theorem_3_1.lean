-- Prove2me | Theorems.Thm_InteractionElim_Main_theorem_3_1
-- name    : InteractionElim.Main.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:22:57.564039+00:00
-- url     : https://prove2.me/theorems/9342be8d-748e-40da-8d3d-f378b4607726
-- title:
--   Theorem 3.1 — initial teaching matches optimal ongoing interaction: $C_{ad}\asymp C_{pre}\asymp\gamma\sum_jF(W_j)$, $C_{lin}\asymp\gamma\sum_jG(W_j)$, with a uniform implementation
-- statement:
--   There are universal constants $c,C>0$ such that every workflow instance of §2 in the regime (2.8) (either branch) satisfies
--   $$
--   c\gamma\sum_jF(W_j)\le C_{ad}\le C_{pre}\le C\gamma\sum_jF(W_j), \tag{3.1}
--   $$
--   $$
--   c\gamma\sum_jG(W_j)\le C_{lin}\le C\gamma\sum_jG(W_j). \tag{3.2}
--   $$
--   The initial-teaching upper bound has a uniform implementation in time $2^{O(2^k)}\mathrm{poly}(N,L)$, including construction and decoding, where $k=\max_jr_j$; it uses at most $O(RL\log(RL)\log R)$ actual tool calls on every path. In particular it is a polynomial-time constant approximation if $2^k=O(\log N)$.
--
--   Formally, $c$, $C$ and one program of the bit-cost machine are fixed before the instance, and for every instance in (2.8) the program's induced protocol is reliable, admissible, initial-teaching, has fee at most $C\gamma\sum_jF(W_j)$, runs in at most $C\,2^{C2^k}(N+L+2)^C$ machine steps on every path of every world (all decisions of parser, agent and expert, each recomputed from the explicit input of bit length $N$), and makes at most $C\,R L\ln(RL)\ln R$ calls on every path.
--
--   The theorem says that an expert who teaches once, at the start, from its record alone loses only a constant factor against arbitrary ongoing interaction, under the same pointwise reliability and the same actual-fee objective, and that the optimal fee is the explicit finite geometric quantity $\gamma\sum_jF(W_j)$.
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
--   - reading: 'In particular it is a polynomial-time constant approximation if 2^k = O(log N)' → no separate conjunct; reason: it follows from the time bound: 2^k ≤ a·log₂N gives 2^{C·2^k} ≤ N^{Ca}
--   - reading: 'The initial-teaching upper bound has a uniform implementation' → the program's induced protocol is reliable, admissible, InitialTeaching and has fee ≤ CγΣ_jF(W_j); reason: the implemented object is the protocol witnessing C_pre ≤ CγΣ_jF(W_j)
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 6, Theorem 3.1, Eqs. (3.1)-(3.2)

import Mathlib
import Definitions.Def_InteractionElim_Main_Machine

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem theorem_3_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ prog : Program, ∀ I : Instance, I.Regime →
        (ENNReal.ofReal (c * I.γ * I.Φ) ≤ Cad I ∧ Cad I ≤ Cpre I ∧
          Cpre I ≤ ENNReal.ofReal (C * I.γ * I.Φ)) ∧
        (ENNReal.ofReal (c * I.γ * I.sumG) ≤ Clin I ∧
          Clin I ≤ ENNReal.ofReal (C * I.γ * I.sumG)) ∧
        (Reliable (inducedProtocol prog I) ∧ Admissible (inducedProtocol prog I) ∧
          InitialTeaching (inducedProtocol prog I) ∧
          fee (inducedProtocol prog I) ≤ ENNReal.ofReal (C * I.γ * I.Φ) ∧
          (∀ x u ω, implTime prog I x u ω ≤
            ENNReal.ofReal (C * (2 : ℝ) ^ (C * (2 : ℝ) ^ I.k) * ((I.N : ℝ) + I.L + 2) ^ C)) ∧
          (∀ x u ω t, ((run (inducedProtocol prog I) x u ω t).totalCalls : ℝ) ≤
            C * I.R * I.L * Real.log ((I.R : ℝ) * I.L) * Real.log I.R)) := by sorry

end InteractionElim.Main
