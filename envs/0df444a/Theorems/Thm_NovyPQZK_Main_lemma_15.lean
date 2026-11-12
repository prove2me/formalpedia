-- Prove2me | Theorems.Thm_NovyPQZK_Main_lemma_15
-- name    : NovyPQZK.Main.lemma_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:39:58.830821+00:00
-- url     : https://prove2.me/theorems/29102e66-a7cf-4c8f-bfe1-a5e5c023ad4b
-- title:
--   Lemma 15 — the adversary S_P rarely aborts when the prover cheats well
-- statement:
--   Let $V$ be the honest verifier of $\mathrm{Hamiltonian\text{-}cycle}_\Pi$ and $\Pi$ a publicly verifiable, post-quantum computational open-once binding bit commitment scheme with unique openings. Let $P$ be a QPT (possibly malicious) prover and $G\notin\mathrm{hamcycle}$ a graph with $\Pr[1\leftarrow[P(1^n,G)\rightleftarrows V(1^n,G)]] = 1-q(n)$. Then the adversary $S_P$ satisfies, for a negligible $\nu$ and every $n$,
--
--   $$\Pr[\perp\leftarrow S_P(1^n)]\ \le\ 2\sqrt{2q(n)}+4q(n)+\nu(n).$$
--
--   With Theorem 8's counting argument this turns a prover cheating with probability above $14/15$ into an Open-Both adversary.
--
--   Differences from the source:
--   - reading: QPT algorithm: a uniform family of polynomial-size quantum circuits (p. 15); adversaries carry auxiliary quantum states (pp. 7, 28) → IsQPT / IsQPT₂ / IsQPTChan₂: non-uniform families of polynomial size over all unitaries on at most two qubits, with a polynomial-size quantum advice state; reason: p. 7 names security against non-uniform adversaries with quantum advice as what the inverter needs (finding I3); one model for every adversary, prover, verifier and simulator; exact gates because exact rewinding needs them
--   - encoding: probabilistic polynomial-time (PPT) protocols (Definition 4) → Party.IsPPT: polynomial-time TM2 machines for the next message and for the coin ranges, all coins drawn at the start uniformly from {0, …, m − 1}, every message of length polynomial in the party's input; reason: a fair-coin PPT machine is the case m = 2; exact uniform sampling over {0, …, m − 1} is the primitive Protocol 18 needs for σ ∈ S_η
--   - encoding: classical messages, openings, tuples of openings → bit strings; tuples written with the self-delimiting pack; a quantum party outputs a string of any length through fixed wires, decoded with unpack; reason: every string and every tuple can be sent or output; nothing is excluded
--   - encoding: interactive committing phase; the quantum sender keeps a quantum memory → rounds n rounds, the receiver speaking first in each (empty messages allowed); the sender is a QStrategy whose state persists from step to step, with incoming messages written into its wires and outgoing ones measured; reason: every alternating protocol has this form; measurements of the outgoing wires are the only classical outputs, as on p. 14
--   - encoding: Protocol 18 on G with |V(G)| = η, vertices 1, …, η, σ ∈_R S_η → vertices 0, …, η − 1; x = pack [1^η, upper-triangular bits in the order of I_η]; σ from one coin of range η! (Lehmer decoding); one block of S_com coins per position and bit value; responses pack [σ, m, u] (ch = 0) and pack [σ(H), openings] (ch = 1); an x that is not a graph is rejected; reason: the protocol as printed, with its sampling and message formats made explicit
--   - encoding: QPT prover P and graph G ∉ hamcycle with Pr[1 ← [P(1^n, G) ⇄ V(1^n, G)]] = 1 − q(n) → Ps : ℕ → QStrategy with IsQPT, x with decodeGraph x ≠ none and no witness; q(n) written out as 1 − (protocol18 Cm).cheatAccept (Ps n) n x; reason: the same quantities
--   - encoding: S_P, steps (1)–(8), with c-P_ch = Σ_t |t⟩⟨t| ⊗ P_{ch,t}, Ver-CH_ch, Ver-COM and the measurement of register A → spAbortProb: the prover's step rounds n with ch written in is c-P_ch (the transcript is classical and summed over); registers P A are the wires it measures; measuring A measures the opening part (m, u) of the response; computed with the honest verifier's coins; reason: R_com at the position (c, d) of step (2) is honest with independent uniform coins, so the joint distribution in steps (2)–(6) is the same for every (c, d)
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §7.1 p. 47, Lemma 15

import Mathlib
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_NovyPQZK_Main_Binding
import Definitions.Def_NovyPQZK_Main_SP

namespace NovyPQZK.Main

theorem lemma_15 (Cm : CommitmentScheme) (hppt : Cm.IsPPT) (hbit : Cm.IsBit)
    (hpv : Cm.IsPubliclyVerifiable) (hoob : Cm.IsOpenOnceBinding) (huo : Cm.HasUniqueOpenings)
    (Ps : ℕ → QStrategy) (hPs : IsQPT Ps) (x : Bits) (hG : (decodeGraph x).isSome = true)
    (hx : ∀ w, hamRel x w = false) :
    ∃ ν : ℕ → ℝ, CompNonlocal.Negligible ν ∧ ∀ n,
      spAbortProb Cm (Ps n) n x ≤
        2 * Real.sqrt (2 * (1 - (protocol18 Cm).cheatAccept (Ps n) n x)) +
          4 * (1 - (protocol18 Cm).cheatAccept (Ps n) n x) + ν n := by sorry

end NovyPQZK.Main
