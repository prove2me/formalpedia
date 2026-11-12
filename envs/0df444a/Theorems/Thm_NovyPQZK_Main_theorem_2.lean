-- Prove2me | Theorems.Thm_NovyPQZK_Main_theorem_2
-- name    : NovyPQZK.Main.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:36:55.188055+00:00
-- url     : https://prove2.me/theorems/bec1bfbe-4315-4c07-94fd-922a0ebe5c47
-- title:
--   Theorem 2 (main result #2) — post-quantum one-way permutations give perfect zero-knowledge arguments with soundness error 14/15 for all NP
-- statement:
--   Assume post-quantum one-way permutations exist: let $\pi$ be a permutation family, computable in polynomial time, such that every QPT algorithm (with quantum advice) inverts $\pi_n$ on a uniform image with negligible probability. Then for every NP relation $R$ there is an interactive argument system $(P,V)$ with
--
--   1. honest $P$ and $V$ classical uniform probabilistic polynomial time;
--   2. completeness: $\Pr[1\leftarrow[P(1^n,x,w)\rightleftarrows V(1^n,x)]]\ge1-\mu(n)$ for a negligible $\mu$, every $n$ and $(x,w)\in R$;
--   3. soundness error $14/15$ against QPT provers: for every QPT prover family and polynomially bounded inputs $x_n$, eventually $x_n\notin L_R$ implies $\Pr[\text{accept}]\le 14/15$;
--   4. post-quantum perfect zero knowledge: every QPT verifier $V^*$ has a QPT simulator, with the same numbers of auxiliary input and output qubits, whose channel equals $V^*$'s channel after interacting with $P$, for every $n$, every $(x,w)\in R$ and every input state.
--
--   $$\exists\ \text{PQ-OWP}\ \Longrightarrow\ \forall R\in\mathrm{NP}:\ \exists (P,V)\ \text{efficient, complete, sound } (14/15),\ \text{post-quantum perfect ZK}.$$
--
--   It is Theorem 6 instantiated with novy (Theorem 1), and was previously known only for classical adversaries [NOV+98].
--
--   Differences from the source:
--   - reading: Definition 13: for any QPT A, Pr_x[π_n(A_n(π_n(x))) = π_n(x)] ≤ negl(n) → IsPQOneWayPermutation π: π computable in deterministic polynomial time, and the bound for every IsQPT inverter (with quantum advice); reason: as printed Definition 13 omits computability and its hypothesis holds unconditionally (finding I1); advice per p. 7 (finding I3)
--   - reading: there exists a post-quantum perfect zero-knowledge argument system with soundness error 14/15 for all NP → for every NP relation R there is A : ArgSystem with A.IsEfficient ∧ A.IsComplete R ∧ A.IsSoundArgument R (fun _ => 14/15) ∧ A.IsPQPerfectZK R; reason: completeness is the first clause of Definition 15; honest prover and verifier are efficient (without an efficient verifier the claim is trivial: V decides x ∈ L by brute force)
--   - reading: sound with soundness error s(n): Pr[1 ← [P(1^n, x) ⇄ V(1^n, x)]] ≤ s(n) for all QPT P, auxiliary input ρ and x ∉ L (Definition 15) → IsSoundArgument: for every IsQPT prover family and every input sequence x_n of length polynomial in n, ∃ n₀, ∀ n ≥ n₀, x_n ∉ L → Pr[accept] ≤ s(n); reason: the every-n form is false (finding I2); the proof (p. 48, (3) with Lemma 15) gives this eventual form; taking n₀ per fixed x alone would let a verifier decide x by brute force once n ≥ 2^{poly(|x|)}, making Theorem 2 hold unconditionally
--   - reading: QPT algorithm: a uniform family of polynomial-size quantum circuits (p. 15); adversaries carry auxiliary quantum states (pp. 7, 28) → IsQPT / IsQPT₂ / IsQPTChan₂: non-uniform families of polynomial size over all unitaries on at most two qubits, with a polynomial-size quantum advice state; reason: p. 7 names security against non-uniform adversaries with quantum advice as what the inverter needs (finding I3); one model for every adversary, prover, verifier and simulator; exact gates because exact rewinding needs them
--   - encoding: probabilistic polynomial-time (PPT) protocols (Definition 4) → Party.IsPPT: polynomial-time TM2 machines for the next message and for the coin ranges, all coins drawn at the start uniformly from {0, …, m − 1}, every message of length polynomial in the party's input; reason: a fair-coin PPT machine is the case m = 2; exact uniform sampling over {0, …, m − 1} is the primitive Protocol 18 needs for σ ∈ S_η
--   - encoding: an NP relation R_L (p. 43) → R : Bits → Bits → Bool decidable in polynomial time on pack [x, w], witnesses of length polynomial in |x|; reason: the standard meaning of 'w certifies in polynomial time that x ∈ L'
--   - encoding: classical messages, openings, tuples of openings → bit strings; tuples written with the self-delimiting pack; a quantum party outputs a string of any length through fixed wires, decoded with unpack; reason: every string and every tuple can be sent or output; nothing is excluded
--   - encoding: interactive committing phase; the quantum sender keeps a quantum memory → rounds n rounds, the receiver speaking first in each (empty messages allowed); the sender is a QStrategy whose state persists from step to step, with incoming messages written into its wires and outgoing ones measured; reason: every alternating protocol has this form; measurements of the outgoing wires are the only classical outputs, as on p. 14
--   - encoding: Φ^n_{x,w} = Ψ^n_x as channels from V to VW; the same numbers of auxiliary input and output qubits (Definition 16, Fig. 4) → realChannel: the verifier's whole register after the run, averaged over all outcomes; the simulator is a QChannelAlg (one unitary circuit with advice, input on its first inQ qubits, output its first outQ qubits, intermediate measurements deferred); equality on every density matrix for every n and (x, w) ∈ R; inQ and outQ agree for every n and |x|; reason: equality on all of D(V) is equality of channels; deferring measurements loses no QPT simulator
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §1.1 p. 4, Theorem 2 (derived on p. 44 from Theorems 1 and 6)

import Mathlib
import Definitions.Def_NovyPQZK_Main_OWP
import Definitions.Def_NovyPQZK_Main_Argument

namespace NovyPQZK.Main

theorem theorem_2 (π : PermFamily) (hπ : IsPQOneWayPermutation π) :
    ∀ R : Bits → Bits → Bool, IsNPRelation R →
      ∃ A : ArgSystem, A.IsEfficient ∧ A.IsComplete R ∧ A.IsSoundArgument R (fun _ => 14 / 15) ∧
        A.IsPQPerfectZK R := by sorry

end NovyPQZK.Main
