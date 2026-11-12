-- Prove2me | Theorems.Thm_NovyPQZK_Main_theorem_8
-- name    : NovyPQZK.Main.theorem_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:38:09.613258+00:00
-- url     : https://prove2.me/theorems/1f069704-922f-4c40-92a9-63de237cf73e
-- title:
--   Theorem 8 — Hamiltonian-cycle_Π is an argument for hamcycle with soundness error 14/15
-- statement:
--   Let $\Pi$ be a publicly verifiable classical bit commitment scheme with unique openings. If $\Pi$ is post-quantum computational open-once binding, then Blum's protocol $\mathrm{Hamiltonian\text{-}cycle}_\Pi$ (Protocol 18) is an argument system for hamcycle with soundness error $14/15$: for every QPT prover family $P^*$ and every sequence of inputs $x_n$ of polynomial length, for all sufficiently large $n$ with $x_n\notin\mathrm{hamcycle}$,
--
--   $$\Pr\big[1\leftarrow[P^*_n(1^n,x_n)\rightleftarrows V(1^n,x_n)]\big]\le\frac{14}{15}.$$
--
--   Soundness against quantum provers is the hard part: rewinding the prover to get two answers is not possible in general, and computational binding alone does not prevent opening a bit of the prover's choice.
--
--   Differences from the source:
--   - reading: sound with soundness error s(n): Pr[1 ← [P(1^n, x) ⇄ V(1^n, x)]] ≤ s(n) for all QPT P, auxiliary input ρ and x ∉ L (Definition 15) → IsSoundArgument: for every IsQPT prover family and every input sequence x_n of length polynomial in n, ∃ n₀, ∀ n ≥ n₀, x_n ∉ L → Pr[accept] ≤ s(n); reason: the every-n form is false (finding I2); the proof (p. 48, (3) with Lemma 15) gives this eventual form; taking n₀ per fixed x alone would let a verifier decide x by brute force once n ≥ 2^{poly(|x|)}, making Theorem 2 hold unconditionally
--   - reading: Hamiltonian-cycle_Π is an argument system for hamcycle with soundness error 14/15 → (protocol18 Cm).IsSoundArgument hamRel (fun _ => 14/15); reason: Definition 15 calls a proof system an argument system when its soundness condition holds for all QPT P; completeness is a separate clause, and Theorem 8 assumes no correctness of Π
--   - reading: QPT algorithm: a uniform family of polynomial-size quantum circuits (p. 15); adversaries carry auxiliary quantum states (pp. 7, 28) → IsQPT / IsQPT₂ / IsQPTChan₂: non-uniform families of polynomial size over all unitaries on at most two qubits, with a polynomial-size quantum advice state; reason: p. 7 names security against non-uniform adversaries with quantum advice as what the inverter needs (finding I3); one model for every adversary, prover, verifier and simulator; exact gates because exact rewinding needs them
--   - encoding: probabilistic polynomial-time (PPT) protocols (Definition 4) → Party.IsPPT: polynomial-time TM2 machines for the next message and for the coin ranges, all coins drawn at the start uniformly from {0, …, m − 1}, every message of length polynomial in the party's input; reason: a fair-coin PPT machine is the case m = 2; exact uniform sampling over {0, …, m − 1} is the primitive Protocol 18 needs for σ ∈ S_η
--   - encoding: classical messages, openings, tuples of openings → bit strings; tuples written with the self-delimiting pack; a quantum party outputs a string of any length through fixed wires, decoded with unpack; reason: every string and every tuple can be sent or output; nothing is excluded
--   - encoding: interactive committing phase; the quantum sender keeps a quantum memory → rounds n rounds, the receiver speaking first in each (empty messages allowed); the sender is a QStrategy whose state persists from step to step, with incoming messages written into its wires and outgoing ones measured; reason: every alternating protocol has this form; measurements of the outgoing wires are the only classical outputs, as on p. 14
--   - encoding: Protocol 18 on G with |V(G)| = η, vertices 1, …, η, σ ∈_R S_η → vertices 0, …, η − 1; x = pack [1^η, upper-triangular bits in the order of I_η]; σ from one coin of range η! (Lehmer decoding); one block of S_com coins per position and bit value; responses pack [σ, m, u] (ch = 0) and pack [σ(H), openings] (ch = 1); an x that is not a graph is rejected; reason: the protocol as printed, with its sampling and message formats made explicit
--   - encoding: hamcycle with the cycle definition of p. 44 → hamRel x w: x decodes to a graph and w to a list (s_0, …, s_{η−1}) of distinct vertices with s_i s_{i+1 mod η} ∈ E; reason: the paper's definition (differs from Mathlib's SimpleGraph.IsHamiltonian for η ≤ 2)
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §7.1 p. 47, Theorem 8

import Mathlib
import Definitions.Def_NovyPQZK_Main_Binding
import Definitions.Def_NovyPQZK_Main_HamCycle

namespace NovyPQZK.Main

theorem theorem_8 (Cm : CommitmentScheme) (hppt : Cm.IsPPT) (hbit : Cm.IsBit)
    (hpv : Cm.IsPubliclyVerifiable) (huo : Cm.HasUniqueOpenings) (hoob : Cm.IsOpenOnceBinding) :
    (protocol18 Cm).IsSoundArgument hamRel (fun _ => 14 / 15) := by sorry

end NovyPQZK.Main
