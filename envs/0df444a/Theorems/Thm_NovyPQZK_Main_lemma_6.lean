-- Prove2me | Theorems.Thm_NovyPQZK_Main_lemma_6
-- name    : NovyPQZK.Main.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:37:31.586495+00:00
-- url     : https://prove2.me/theorems/5ed8220a-56d8-4024-b976-dc1903c0e8eb
-- title:
--   Lemma 6 — parallel composition preserves collapse-binding and statistical/perfect hiding
-- statement:
--   Let $\Pi$ be a post-quantum computational collapse-binding classical commitment scheme and $k = k(n)$ a polynomially bounded integer. Then the $k$-fold parallel composition $\Pi^k$ is post-quantum computational collapse-binding. Moreover, if $\Pi$ is statistically (resp. perfectly) hiding, then $\Pi^k$ is statistically (resp. perfectly) hiding.
--
--   $$\Pi\ \text{collapse-binding}\ \Longrightarrow\ \Pi^k\ \text{collapse-binding};\qquad \Pi\ \text{stat./perf. hiding}\ \Longrightarrow\ \Pi^k\ \text{stat./perf. hiding}.$$
--
--   Blum's protocol commits to a whole adjacency matrix in parallel, which is why this lemma is needed for interactive commitments.
--
--   Differences from the source:
--   - reading: QPT algorithm: a uniform family of polynomial-size quantum circuits (p. 15); adversaries carry auxiliary quantum states (pp. 7, 28) → IsQPT / IsQPT₂ / IsQPTChan₂: non-uniform families of polynomial size over all unitaries on at most two qubits, with a polynomial-size quantum advice state; reason: p. 7 names security against non-uniform adversaries with quantum advice as what the inverter needs (finding I3); one model for every adversary, prover, verifier and simulator; exact gates because exact rewinding needs them
--   - encoding: probabilistic polynomial-time (PPT) protocols (Definition 4) → Party.IsPPT: polynomial-time TM2 machines for the next message and for the coin ranges, all coins drawn at the start uniformly from {0, …, m − 1}, every message of length polynomial in the party's input; reason: a fair-coin PPT machine is the case m = 2; exact uniform sampling over {0, …, m − 1} is the primitive Protocol 18 needs for σ ∈ S_η
--   - encoding: classical messages, openings, tuples of openings → bit strings; tuples written with the self-delimiting pack; a quantum party outputs a string of any length through fixed wires, decoded with unpack; reason: every string and every tuple can be sent or output; nothing is excluded
--   - encoding: interactive committing phase; the quantum sender keeps a quantum memory → rounds n rounds, the receiver speaking first in each (empty messages allowed); the sender is a QStrategy whose state persists from step to step, with incoming messages written into its wires and outgoing ones measured; reason: every alternating protocol has this form; measurements of the outgoing wires are the only classical outputs, as on p. 14
--   - encoding: registers S, M, U of the adversary after the committing phase (Experiment 7) → two disjoint wire lists mW (M) and uW (U) chosen with the adversary; m is the contents of M, u is decoded from U; reason: every choice of registers is quantified; decoding U lets an opening of any length be held
--   - encoding: the views of any, possibly unbounded, receiver R are identical / statistically indistinguishable (Definition 6) → for every deterministic receiver strategy (next message from the sender's messages so far), the distributions of its transcript are equal / at statistical distance ≤ μ(n) with μ negligible; reason: a randomized receiver is a mixture of deterministic ones and a deterministic receiver's view is its transcript
--   - encoding: Π^k = (SetUp, S^k_com, R^k_com, S^k_open, R^k_open), messages of a round concatenated (Definition 12) → Public^k_n = pack [1^{k(n)}, Public_n]; each round's message is pack of the k component messages; m = pack [m_1, …, m_k], u = pack [u_1, …, u_k]; reason: the receiver must know k(n); pack is the self-delimiting concatenation
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3.4 p. 26, Lemma 6

import Mathlib
import Definitions.Def_NovyPQZK_Main_Binding

namespace NovyPQZK.Main

theorem lemma_6 (Cm : CommitmentScheme) (hppt : Cm.IsPPT) (hcb : Cm.IsCollapseBinding)
    (k : ℕ → ℕ) (hk : IsPolyBounded k) :
    (Cm.parallel k).IsCollapseBinding ∧
      (Cm.IsStatisticallyHiding → (Cm.parallel k).IsStatisticallyHiding) ∧
      (Cm.IsPerfectlyHiding → (Cm.parallel k).IsPerfectlyHiding) := by sorry

end NovyPQZK.Main
