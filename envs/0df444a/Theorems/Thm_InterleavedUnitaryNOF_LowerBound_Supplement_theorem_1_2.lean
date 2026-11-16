-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_Supplement_theorem_1_2
-- name    : InterleavedUnitaryNOF.LowerBound.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:47:28.345165+00:00
-- url     : https://prove2.me/theorems/75a808b1-3326-4fbb-8bbc-5cf45b99fd7c
-- title:
--   Theorem 1.2 — one-clean-qubit quantum NOF upper bound
-- statement:
--   Fix any published admissible dimension schedule $m(n)$. For every fixed $0<\varepsilon<1/2$, there are a positive integer $L$, a constant $C>0$, and an integer $N\ge2$, all chosen before $n$ and the input, such that for every $n\ge N$ there is an integer $q\ge0$ with $m(n)=2^q$ and the operational Protocol 1 satisfies
--
--   $$\Pr[\text{output}\ne b]\le\varepsilon\quad\text{whenever}\quad\operatorname{IUP}_{m(n)}(x,y,z)=b,$$
--
--   $$\operatorname{cost}=9L\bigl(1+\lceil\log_2 m(n)\rceil\bigr)\le C\log_2 n.$$
--
--   Every gate is unitary on every input, the final measurement is projective, and the probabilities in the error bound come from actual density-matrix evolution and the Born rule. Each independent run uses one initially pure qubit and a maximally mixed target, no prior entanglement, and no additional quantum memory. Charlie produces the final local output. There is no correctness requirement off-promise. The default error $\varepsilon=1/3$ uses $L=100$, giving exactly $900(1+\lceil\log_2 m(n)\rceil)$ communicated qubits. Constants and repetition counts may depend on the fixed schedule and requested error.
--
--   This is the quantum upper-bound companion theorem; it is independent of the proof of the published randomized lower-bound goal. All bit strings, complex near-unitary matrices, trace thresholds and fitting dimension schedules are inherited from the unchanged published IUP definition.
--
--   Differences from the source:
--   - encoding: power-of-two dimensions of order sqrt(n/log n) fitting the input encoding → the published AdmissibleSchedule, with an eventual witness q such that m n = 2^q; reason: every fitting schedule is retained and q only identifies the register dimension
--   - generalization: existence of a bounded-error one-clean-qubit quantum NOF protocol with O(log n) communication → the explicit protocol1 construction is physically valid, has derived Born error at most ε on every promised input, and has exact cost 9L(1+⌈log₂ m(n)⌉); reason: naming the source's own witness (Protocol 1, pp.8–9) with its exact cost asserts more than existence and implies the existence claim of Theorem 1.2
--   - encoding: default error 1/3, 100 runs in Protocol 1, and arbitrary fixed constant error by footnote 1 → all positive errors below 1/2, a length-independent L, and L = 100 when the error is 1/3; reason: the default and the footnote are included in one statement, with constants chosen before input length
--   - encoding: no required answer off the IUP promise → local identity fallback for a matrix failing its own near-unitarity test; reason: operations become total off-promise and remain the exact polar gates on every promised input
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Theorem 1.2, p.3; proof pp.8-9

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Supplement_Protocol1

namespace InterleavedUnitaryNOF.LowerBound.Supplement

/-- Theorem 1.2, p.3, §3 pp.8–9 and footnote 1. Every fixed positive error
below 1/2 is allowed by a constant number of fresh one-clean-qubit runs.
At the default error 1/3 the source witnesses exactly 100 runs. Constants and
the repetition count are chosen before n and all inputs. -/
theorem theorem_1_2 (m : ℕ → ℕ) (hm : AdmissibleSchedule m) :
    ∀ ε : ℝ, 0 < ε → ε < 1/2 →
    ∃ L : ℕ, 0 < L ∧ (ε = 1/3 → L = 100) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N,
    ∃ q : ℕ, m n = 2^q ∧
      (protocol1 n q L).WellFormed ∧
      (protocol1 n q L).cost = 9 * L * (1 + Nat.clog 2 (m n)) ∧
      ((protocol1 n q L).cost : ℝ) ≤ C * Real.logb 2 n ∧
      (protocol1 n q L).Correct (iup (m n)) ε := by sorry

end InterleavedUnitaryNOF.LowerBound.Supplement
