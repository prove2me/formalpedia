-- Prove2me | Theorems.Thm_NovyPQZK_Main_lemma_5
-- name    : NovyPQZK.Main.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:37:34.719805+00:00
-- url     : https://prove2.me/theorems/a502ee4b-3bd9-49f8-adef-ee166795280f
-- title:
--   Lemma 5 — unique openings and open-once binding imply collapse-binding
-- statement:
--   Let $\Pi$ be a classical bit commitment scheme with unique openings. If $\Pi$ is post-quantum computational open-once binding, then $\Pi$ is post-quantum computational collapse-binding: for every QPT sender and every choice of its message and opening registers $M,U$,
--
--   $$\Pr[\text{Collapse-Binding}_{\Pi,S}(n)=1]\le\tfrac12+\mathrm{negl}(n),$$
--
--   i.e. after a successful verification of the opening, measuring the message register cannot be detected. It is the property that makes the soundness of Blum's argument survive quantum provers.
--
--   Differences from the source:
--   - reading: QPT algorithm: a uniform family of polynomial-size quantum circuits (p. 15); adversaries carry auxiliary quantum states (pp. 7, 28) → IsQPT / IsQPT₂ / IsQPTChan₂: non-uniform families of polynomial size over all unitaries on at most two qubits, with a polynomial-size quantum advice state; reason: p. 7 names security against non-uniform adversaries with quantum advice as what the inverter needs (finding I3); one model for every adversary, prover, verifier and simulator; exact gates because exact rewinding needs them
--   - encoding: probabilistic polynomial-time (PPT) protocols (Definition 4) → Party.IsPPT: polynomial-time TM2 machines for the next message and for the coin ranges, all coins drawn at the start uniformly from {0, …, m − 1}, every message of length polynomial in the party's input; reason: a fair-coin PPT machine is the case m = 2; exact uniform sampling over {0, …, m − 1} is the primitive Protocol 18 needs for σ ∈ S_η
--   - encoding: classical messages, openings, tuples of openings → bit strings; tuples written with the self-delimiting pack; a quantum party outputs a string of any length through fixed wires, decoded with unpack; reason: every string and every tuple can be sent or output; nothing is excluded
--   - encoding: interactive committing phase; the quantum sender keeps a quantum memory → rounds n rounds, the receiver speaking first in each (empty messages allowed); the sender is a QStrategy whose state persists from step to step, with incoming messages written into its wires and outgoing ones measured; reason: every alternating protocol has this form; measurements of the outgoing wires are the only classical outputs, as on p. 14
--   - encoding: registers S, M, U of the adversary after the committing phase (Experiment 7) → two disjoint wire lists mW (M) and uW (U) chosen with the adversary; m is the contents of M, u is decoded from U; reason: every choice of registers is quantified; decoding U lets an opening of any length be held
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3.4 p. 26, Lemma 5

import Mathlib
import Definitions.Def_NovyPQZK_Main_Binding

namespace NovyPQZK.Main

theorem lemma_5 (Cm : CommitmentScheme) (hppt : Cm.IsPPT) (hbit : Cm.IsBit)
    (huo : Cm.HasUniqueOpenings) (hoob : Cm.IsOpenOnceBinding) :
    Cm.IsCollapseBinding := by sorry

end NovyPQZK.Main
