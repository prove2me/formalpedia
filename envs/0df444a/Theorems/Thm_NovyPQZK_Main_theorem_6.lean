-- Prove2me | Theorems.Thm_NovyPQZK_Main_theorem_6
-- name    : NovyPQZK.Main.theorem_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:37:36.568833+00:00
-- url     : https://prove2.me/theorems/6af81110-2098-4932-9d01-5bf8bdedcfdd
-- title:
--   Theorem 6 — from a suitable bit commitment, post-quantum perfect zero-knowledge arguments with soundness error 14/15 for all NP
-- statement:
--   Assume there exists a publicly verifiable classical bit commitment scheme that has unique openings and is both post-quantum computational open-once binding and perfectly hiding (and correct). Then every NP relation $R$ has a post-quantum perfect zero-knowledge argument system with soundness error $14/15$: an interactive protocol $(P,V)$ with efficient honest parties such that
--
--   $$\text{complete},\qquad \Pr[P^*\text{ convinces }V\text{ of }x\notin L_R]\le\tfrac{14}{15}\ \text{(eventually)},\qquad \Phi^n_{x,w}=\Psi^n_x .$$
--
--   It follows from Theorem 8, Theorem 9 and the NP-completeness of hamcycle.
--
--   Differences from the source:
--   - reading: a publicly verifiable classical bit commitment scheme (Definitions 4, 5) → adds Cm.IsCorrect: the honest opening of an honest commitment to m ∈ M is accepted for all coins; reason: Definition 4 states no correctness; without it the construction of the proof (Protocol 18) is not complete (finding I5); novy is perfectly correct
--   - reading: there exists a post-quantum perfect zero-knowledge argument system with soundness error 14/15 for all NP → for every NP relation R there is A : ArgSystem with A.IsEfficient ∧ A.IsComplete R ∧ A.IsSoundArgument R (fun _ => 14/15) ∧ A.IsPQPerfectZK R; reason: completeness is the first clause of Definition 15; honest prover and verifier are efficient (without an efficient verifier the claim is trivial: V decides x ∈ L by brute force)
--   - reading: sound with soundness error s(n): Pr[1 ← [P(1^n, x) ⇄ V(1^n, x)]] ≤ s(n) for all QPT P, auxiliary input ρ and x ∉ L (Definition 15) → IsSoundArgument: for every IsQPT prover family and every input sequence x_n of length polynomial in n, ∃ n₀, ∀ n ≥ n₀, x_n ∉ L → Pr[accept] ≤ s(n); reason: the every-n form is false (finding I2); the proof (p. 48, (3) with Lemma 15) gives this eventual form; taking n₀ per fixed x alone would let a verifier decide x by brute force once n ≥ 2^{poly(|x|)}, making Theorem 2 hold unconditionally
--   - reading: QPT algorithm: a uniform family of polynomial-size quantum circuits (p. 15); adversaries carry auxiliary quantum states (pp. 7, 28) → IsQPT / IsQPT₂ / IsQPTChan₂: non-uniform families of polynomial size over all unitaries on at most two qubits, with a polynomial-size quantum advice state; reason: p. 7 names security against non-uniform adversaries with quantum advice as what the inverter needs (finding I3); one model for every adversary, prover, verifier and simulator; exact gates because exact rewinding needs them
--   - encoding: probabilistic polynomial-time (PPT) protocols (Definition 4) → Party.IsPPT: polynomial-time TM2 machines for the next message and for the coin ranges, all coins drawn at the start uniformly from {0, …, m − 1}, every message of length polynomial in the party's input; reason: a fair-coin PPT machine is the case m = 2; exact uniform sampling over {0, …, m − 1} is the primitive Protocol 18 needs for σ ∈ S_η
--   - encoding: an NP relation R_L (p. 43) → R : Bits → Bits → Bool decidable in polynomial time on pack [x, w], witnesses of length polynomial in |x|; reason: the standard meaning of 'w certifies in polynomial time that x ∈ L'
--   - encoding: classical messages, openings, tuples of openings → bit strings; tuples written with the self-delimiting pack; a quantum party outputs a string of any length through fixed wires, decoded with unpack; reason: every string and every tuple can be sent or output; nothing is excluded
--   - encoding: interactive committing phase; the quantum sender keeps a quantum memory → rounds n rounds, the receiver speaking first in each (empty messages allowed); the sender is a QStrategy whose state persists from step to step, with incoming messages written into its wires and outgoing ones measured; reason: every alternating protocol has this form; measurements of the outgoing wires are the only classical outputs, as on p. 14
--   - encoding: the views of any, possibly unbounded, receiver R are identical / statistically indistinguishable (Definition 6) → for every deterministic receiver strategy (next message from the sender's messages so far), the distributions of its transcript are equal / at statistical distance ≤ μ(n) with μ negligible; reason: a randomized receiver is a mixture of deterministic ones and a deterministic receiver's view is its transcript
--   - encoding: Φ^n_{x,w} = Ψ^n_x as channels from V to VW; the same numbers of auxiliary input and output qubits (Definition 16, Fig. 4) → realChannel: the verifier's whole register after the run, averaged over all outcomes; the simulator is a QChannelAlg (one unitary circuit with advice, input on its first inQ qubits, output its first outQ qubits, intermediate measurements deferred); equality on every density matrix for every n and (x, w) ∈ R; inQ and outQ agree for every n and |x|; reason: equality on all of D(V) is equality of channels; deferring measurements loses no QPT simulator
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §7 p. 44, Theorem 6

import Mathlib
import Definitions.Def_NovyPQZK_Main_Binding
import Definitions.Def_NovyPQZK_Main_Argument

namespace NovyPQZK.Main

theorem theorem_6
    (hcom : ∃ Cm : CommitmentScheme, Cm.IsPPT ∧ Cm.IsBit ∧ Cm.IsCorrect ∧ Cm.IsPubliclyVerifiable ∧
      Cm.HasUniqueOpenings ∧ Cm.IsOpenOnceBinding ∧ Cm.IsPerfectlyHiding) :
    ∀ R : Bits → Bits → Bool, IsNPRelation R →
      ∃ A : ArgSystem, A.IsEfficient ∧ A.IsComplete R ∧ A.IsSoundArgument R (fun _ => 14 / 15) ∧
        A.IsPQPerfectZK R := by sorry

end NovyPQZK.Main
