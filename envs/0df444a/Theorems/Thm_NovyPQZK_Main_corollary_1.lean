-- Prove2me | Theorems.Thm_NovyPQZK_Main_corollary_1
-- name    : NovyPQZK.Main.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:38:48.25547+00:00
-- url     : https://prove2.me/theorems/cdc55116-4c08-4000-96cf-9b04921cb241
-- title:
--   Corollary 1 — π-binding implies sum-binding and collapse-binding for novy
-- statement:
--   Let novy be instantiated with a permutation family $\pi$ (computable in polynomial time). If novy is computational $\pi$-binding — no QPT sender, after interactive hashing with an honest Rachel, outputs preimages of both $y_0(t)$ and $y_1(t)$ except with negligible probability — then novy is post-quantum computational sum-binding and post-quantum computational collapse-binding:
--
--   $$\Pr[\text{Sum-Binding}_{\mathrm{novy},S}(n)=1]\le\tfrac12+\mathrm{negl}(n),\qquad \Pr[\text{Collapse-Binding}_{\mathrm{novy},S}(n)=1]\le\tfrac12+\mathrm{negl}(n)$$
--
--   for every QPT $S$.
--
--   Differences from the source:
--   - reading: novy instantiated with a permutation family π → the hypothesis π.IsPolyTime (π_n computable in deterministic polynomial time); reason: Definition 4 requires novy's five protocols to be PPT, which needs π computable; finding I1
--   - reading: QPT algorithm: a uniform family of polynomial-size quantum circuits (p. 15); adversaries carry auxiliary quantum states (pp. 7, 28) → IsQPT / IsQPT₂ / IsQPTChan₂: non-uniform families of polynomial size over all unitaries on at most two qubits, with a polynomial-size quantum advice state; reason: p. 7 names security against non-uniform adversaries with quantum advice as what the inverter needs (finding I3); one model for every adversary, prover, verifier and simulator; exact gates because exact rewinding needs them
--   - encoding: classical messages, openings, tuples of openings → bit strings; tuples written with the self-delimiting pack; a quantum party outputs a string of any length through fixed wires, decoded with unpack; reason: every string and every tuple can be sent or output; nothing is excluded
--   - encoding: interactive committing phase; the quantum sender keeps a quantum memory → rounds n rounds, the receiver speaking first in each (empty messages allowed); the sender is a QStrategy whose state persists from step to step, with incoming messages written into its wires and outgoing ones measured; reason: every alternating protocol has this form; measurements of the outgoing wires are the only classical outputs, as on p. 14
--   - encoding: registers S, M, U of the adversary after the committing phase (Experiment 7) → two disjoint wire lists mW (M) and uW (U) chosen with the adversary; m is the contents of M, u is decoded from U; reason: every choice of registers is quantified; decoding U lets an opening of any length be held
--   - encoding: novy (box on p. 2, Fig. 1) → Public_n = 1^n (1^1 at n = 0, where the scheme is undefined); (n − 1) + 1 rounds, Rachel sending the empty string in the last; opening u = pack [x, y]; Sam aborts (sends the empty string from then on) on a challenge not of the form 0^{i−1}‖1‖r; reason: the source leaves these unspecified; aborting does not depend on b
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3.4 p. 27, Corollary 1

import Mathlib
import Definitions.Def_NovyPQZK_Main_Novy

namespace NovyPQZK.Main

theorem corollary_1 (π : PermFamily) (hπ : π.IsPolyTime) (hbind : IsPiBinding π) :
    (novy π).IsSumBinding ∧ (novy π).IsCollapseBinding := by sorry

end NovyPQZK.Main
