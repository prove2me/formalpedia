-- Prove2me | Theorems.Thm_KTUnitary_Synth_proposition_4_8
-- name    : KTUnitary.Synth.proposition_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:39:58.389847+00:00
-- url     : https://prove2.me/theorems/4cc2971c-223f-4107-a467-54f4686757fc
-- title:
--   Proposition 4.8 — $\mathsf{BQPSPACE}^L=\mathsf{BQUPSPACE}^L=\mathsf{PSPACE}^L$
-- statement:
--   For every language $L$,
--   $$\mathsf{BQPSPACE}^L=\mathsf{BQUPSPACE}^L=\mathsf{PSPACE}^L,$$
--   as classes of promise problems, where the quantum classes use the oracle gates $U_m|x,b\rangle=|x,b\oplus L(x)\rangle$ of Definition 4.4 and $\mathsf{PSPACE}^L$ counts the oracle query tape in the space bound.
--
--   This is the relativized form of $\mathsf{BQPSPACE}=\mathsf{BQUPSPACE}=\mathsf{PSPACE}$.
--
--   Differences from the source:
--   - reading: BQP^𝒪, BQUPSPACE^𝒪, BQPSPACE^L, PSPACE^L → classes of promise problems; a language A is the pair (A, Aᶜ); reason: Definition 4.6 defines the quantum classes on promise problems
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
--   - encoding: L used as an oracle → its unitary embedding emb L, with U_0 = 1; reason: "we may sometimes overload L to mean both the language and its unitary embedding" (p. 16); U_0 is not defined in the paper
--   - reading: a designated output qubit or register of a uniform family → the wire(s) are part of the family: the uniformity machine prints them with the circuit, and a register has distinct wires; reason: Definition 4.5 makes the machine output the family; a wire chosen outside the description would be non-uniform advice (it would decide every unary language), against Definition 4.6 and the proof of Proposition 5.8, which measures a fixed first qubit
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Proposition 4.8, p. 15

import Mathlib
import Definitions.Def_KTUnitary_Synth_BQPSPACE
import Definitions.Def_KTUnitary_Synth_BQUPSPACEplain
import Definitions.Def_KTUnitary_Synth_PromisePSPACE

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Proposition 4.8** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Proposition 4.8, p. 15). For all languages `L`,
`BQPSPACE^L = BQUPSPACE^L = PSPACE^L`.

**Formalization Note** The three classes are classes of promise problems (Definition 4.6 is about
promise problems), and `PSPACE^L` is `PromisePSPACE L`. `BQUPSPACE^L` has the oracle gates of
Definition 4.4 (`BQUPSPACEplain L`). -/
theorem proposition_4_8 (L : Oracle) :
    BQPSPACE L = BQUPSPACEplain L ∧ BQUPSPACEplain L = PromisePSPACE L := by sorry

end KTUnitary.Synth
