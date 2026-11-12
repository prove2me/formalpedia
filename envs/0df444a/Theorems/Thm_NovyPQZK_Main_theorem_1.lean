-- Prove2me | Theorems.Thm_NovyPQZK_Main_theorem_1
-- name    : NovyPQZK.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:38:51.697062+00:00
-- url     : https://prove2.me/theorems/f2f0a976-9a00-479d-aa29-f002fe15a311
-- title:
--   Theorem 1 (main result #1) — from a post-quantum one-way permutation, novy is sum-, collapse- and open-once binding and perfectly hiding
-- statement:
--   Let $\pi$ be a post-quantum one-way permutation. Then the novy bit commitment scheme instantiated with $\pi$ is
--
--   1. post-quantum computational sum-binding,
--   2. post-quantum computational collapse-binding,
--   3. post-quantum computational open-once binding, and
--   4. perfectly hiding (against every, possibly unbounded, receiver).
--
--   $$\mathrm{novy}_\pi:\quad \Pr[\text{Sum}]\le\tfrac12+\mathrm{negl},\quad \Pr[\text{Collapse}]\le\tfrac12+\mathrm{negl},\quad \Pr[\text{Open-Both}]\le\mathrm{negl},\quad \text{views identical}.$$
--
--   It is the first post-quantum statistically hiding commitment shown sum-binding from a generic assumption; Theorem 2 combines it with Theorem 6.
--
--   Differences from the source:
--   - reading: Definition 13: for any QPT A, Pr_x[π_n(A_n(π_n(x))) = π_n(x)] ≤ negl(n) → IsPQOneWayPermutation π: π computable in deterministic polynomial time, and the bound for every IsQPT inverter (with quantum advice); reason: as printed Definition 13 omits computability and its hypothesis holds unconditionally (finding I1); advice per p. 7 (finding I3)
--   - reading: QPT algorithm: a uniform family of polynomial-size quantum circuits (p. 15); adversaries carry auxiliary quantum states (pp. 7, 28) → IsQPT / IsQPT₂ / IsQPTChan₂: non-uniform families of polynomial size over all unitaries on at most two qubits, with a polynomial-size quantum advice state; reason: p. 7 names security against non-uniform adversaries with quantum advice as what the inverter needs (finding I3); one model for every adversary, prover, verifier and simulator; exact gates because exact rewinding needs them
--   - encoding: classical messages, openings, tuples of openings → bit strings; tuples written with the self-delimiting pack; a quantum party outputs a string of any length through fixed wires, decoded with unpack; reason: every string and every tuple can be sent or output; nothing is excluded
--   - encoding: interactive committing phase; the quantum sender keeps a quantum memory → rounds n rounds, the receiver speaking first in each (empty messages allowed); the sender is a QStrategy whose state persists from step to step, with incoming messages written into its wires and outgoing ones measured; reason: every alternating protocol has this form; measurements of the outgoing wires are the only classical outputs, as on p. 14
--   - encoding: registers S, M, U of the adversary after the committing phase (Experiment 7) → two disjoint wire lists mW (M) and uW (U) chosen with the adversary; m is the contents of M, u is decoded from U; reason: every choice of registers is quantified; decoding U lets an opening of any length be held
--   - encoding: novy (box on p. 2, Fig. 1) → Public_n = 1^n (1^1 at n = 0, where the scheme is undefined); (n − 1) + 1 rounds, Rachel sending the empty string in the last; opening u = pack [x, y]; Sam aborts (sends the empty string from then on) on a challenge not of the form 0^{i−1}‖1‖r; reason: the source leaves these unspecified; aborting does not depend on b
--   - encoding: the views of any, possibly unbounded, receiver R are identical / statistically indistinguishable (Definition 6) → for every deterministic receiver strategy (next message from the sender's messages so far), the distributions of its transcript are equal / at statistical distance ≤ μ(n) with μ negligible; reason: a randomized receiver is a mixture of deterministic ones and a deterministic receiver's view is its transcript
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §1.1 p. 4, Theorem 1 (proof completed on p. 43, §6.4)

import Mathlib
import Definitions.Def_NovyPQZK_Main_Novy

namespace NovyPQZK.Main

theorem theorem_1 (π : PermFamily) (hπ : IsPQOneWayPermutation π) :
    (novy π).IsSumBinding ∧ (novy π).IsCollapseBinding ∧ (novy π).IsOpenOnceBinding ∧
      (novy π).IsPerfectlyHiding := by sorry

end NovyPQZK.Main
