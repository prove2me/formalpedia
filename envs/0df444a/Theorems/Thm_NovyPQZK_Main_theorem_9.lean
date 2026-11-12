-- Prove2me | Theorems.Thm_NovyPQZK_Main_theorem_9
-- name    : NovyPQZK.Main.theorem_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:38:04.170888+00:00
-- url     : https://prove2.me/theorems/eecd0428-6664-4838-ac58-78dc984a5724
-- title:
--   Theorem 9 — perfect hiding makes Hamiltonian-cycle_Π post-quantum perfect zero-knowledge
-- statement:
--   Let $\Pi$ be a classical bit commitment scheme. If $\Pi$ is perfectly hiding, then the argument system $\mathrm{Hamiltonian\text{-}cycle}_\Pi$ is post-quantum perfect zero-knowledge: for every QPT verifier $V^*$ there is a QPT simulator $S_{V^*}$ with the same numbers of auxiliary input and output qubits such that, for every $n$ and every graph $G$ with Hamiltonian cycle $H$,
--
--   $$\Phi^n_{G,H}=\Psi^n_G\quad\text{as channels},$$
--
--   where $\Phi^n_{G,H}(\rho)$ is $V^*$'s final state after interacting with the honest prover on auxiliary input $\rho$ and $\Psi^n_G(\rho)$ is the simulator's output. The simulator never sees $H$.
--
--   Differences from the source:
--   - reading: QPT algorithm: a uniform family of polynomial-size quantum circuits (p. 15); adversaries carry auxiliary quantum states (pp. 7, 28) → IsQPT / IsQPT₂ / IsQPTChan₂: non-uniform families of polynomial size over all unitaries on at most two qubits, with a polynomial-size quantum advice state; reason: p. 7 names security against non-uniform adversaries with quantum advice as what the inverter needs (finding I3); one model for every adversary, prover, verifier and simulator; exact gates because exact rewinding needs them
--   - encoding: probabilistic polynomial-time (PPT) protocols (Definition 4) → Party.IsPPT: polynomial-time TM2 machines for the next message and for the coin ranges, all coins drawn at the start uniformly from {0, …, m − 1}, every message of length polynomial in the party's input; reason: a fair-coin PPT machine is the case m = 2; exact uniform sampling over {0, …, m − 1} is the primitive Protocol 18 needs for σ ∈ S_η
--   - encoding: classical messages, openings, tuples of openings → bit strings; tuples written with the self-delimiting pack; a quantum party outputs a string of any length through fixed wires, decoded with unpack; reason: every string and every tuple can be sent or output; nothing is excluded
--   - encoding: interactive committing phase; the quantum sender keeps a quantum memory → rounds n rounds, the receiver speaking first in each (empty messages allowed); the sender is a QStrategy whose state persists from step to step, with incoming messages written into its wires and outgoing ones measured; reason: every alternating protocol has this form; measurements of the outgoing wires are the only classical outputs, as on p. 14
--   - encoding: Protocol 18 on G with |V(G)| = η, vertices 1, …, η, σ ∈_R S_η → vertices 0, …, η − 1; x = pack [1^η, upper-triangular bits in the order of I_η]; σ from one coin of range η! (Lehmer decoding); one block of S_com coins per position and bit value; responses pack [σ, m, u] (ch = 0) and pack [σ(H), openings] (ch = 1); an x that is not a graph is rejected; reason: the protocol as printed, with its sampling and message formats made explicit
--   - encoding: hamcycle with the cycle definition of p. 44 → hamRel x w: x decodes to a graph and w to a list (s_0, …, s_{η−1}) of distinct vertices with s_i s_{i+1 mod η} ∈ E; reason: the paper's definition (differs from Mathlib's SimpleGraph.IsHamiltonian for η ≤ 2)
--   - encoding: the views of any, possibly unbounded, receiver R are identical / statistically indistinguishable (Definition 6) → for every deterministic receiver strategy (next message from the sender's messages so far), the distributions of its transcript are equal / at statistical distance ≤ μ(n) with μ negligible; reason: a randomized receiver is a mixture of deterministic ones and a deterministic receiver's view is its transcript
--   - encoding: Φ^n_{x,w} = Ψ^n_x as channels from V to VW; the same numbers of auxiliary input and output qubits (Definition 16, Fig. 4) → realChannel: the verifier's whole register after the run, averaged over all outcomes; the simulator is a QChannelAlg (one unitary circuit with advice, input on its first inQ qubits, output its first outQ qubits, intermediate measurements deferred); equality on every density matrix for every n and (x, w) ∈ R; inQ and outQ agree for every n and |x|; reason: equality on all of D(V) is equality of channels; deferring measurements loses no QPT simulator
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §7.2 p. 50, Theorem 9

import Mathlib
import Definitions.Def_NovyPQZK_Main_HamCycle

namespace NovyPQZK.Main

theorem theorem_9 (Cm : CommitmentScheme) (hppt : Cm.IsPPT) (hbit : Cm.IsBit)
    (hph : Cm.IsPerfectlyHiding) :
    (protocol18 Cm).IsPQPerfectZK hamRel := by sorry

end NovyPQZK.Main
