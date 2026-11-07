-- Prove2me | Theorems.Thm_KTUnitary_Synth_proposition_5_8
-- name    : KTUnitary.Synth.proposition_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:37:49.824344+00:00
-- url     : https://prove2.me/theorems/19019686-3bf2-4b75-85f1-9fb274cf0a20
-- title:
--   Proposition 5.8 — unitary classes subsume languages
-- statement:
--   Fix a unitary oracle $\mathcal O$ and a language $L$, and let $\mathcal U$ be the unitary embedding of $L$, $U_n|x,b\rangle=|x,b\oplus L(x)\rangle$. Then
--   1. $L\in\mathsf{BQP}^{\mathcal O}\implies\mathcal U\in\mathsf{unitaryP}^{\mathcal O}$;
--   2. $L\in\mathsf{BQUPSPACE}^{\mathcal O}\implies\mathcal U\in\mathsf{unitaryPSPACE}^{\mathcal O}$,
--
--   where the language classes allow the same oracle gates as Definition 5.5 ($O_n,O_n^*,O_n^\dagger,O_n^T$ and their controlled versions).
--
--   So the unitary classes are conservative extensions of the bounded-error language classes.
--
--   Differences from the source:
--   - reading: BQP^𝒪, BQUPSPACE^𝒪, BQPSPACE^L, PSPACE^L → classes of promise problems; a language A is the pair (A, Aᶜ); reason: Definition 4.6 defines the quantum classes on promise problems
--   - encoding: L used as an oracle → its unitary embedding emb L, with U_0 = 1; reason: "we may sometimes overload L to mean both the language and its unitary embedding" (p. 16); U_0 is not defined in the paper
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
--   - reading: a designated output qubit or register of a uniform family → the wire(s) are part of the family: the uniformity machine prints them with the circuit, and a register has distinct wires; reason: Definition 4.5 makes the machine output the family; a wire chosen outside the description would be non-uniform advice (it would decide every unary language), against Definition 4.6 and the proof of Proposition 5.8, which measures a fixed first qubit
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Proposition 5.8, p. 18

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_BQP
import Definitions.Def_KTUnitary_Synth_BQUPSPACE
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Proposition 5.8** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Proposition 5.8, p. 18; unitary classes subsume languages). Fix a
unitary oracle `𝒪` and language `L`, and let `𝒰` be its unitary embedding. Then
`L ∈ BQP^𝒪 ⟹ 𝒰 ∈ unitaryP^𝒪` and `L ∈ BQUPSPACE^𝒪 ⟹ 𝒰 ∈ unitaryPSPACE^𝒪`, where the unitary
oracle model for the language classes allows the same gates as in Definition 5.5.

**Formalization Note** The language `L` is the promise problem `({s | L s}, {s | L s}ᶜ)`; `BQP 𝒪`
and `BQUPSPACE 𝒪` use all eight oracle gate kinds of Definition 5.5. -/
theorem proposition_5_8 (O : ULang) (L : Oracle) :
    (({s | L s = true}, {s | L s = true}ᶜ) ∈ BQP O → emb L ∈ unitaryP O) ∧
    (({s | L s = true}, {s | L s = true}ᶜ) ∈ BQUPSPACE O → emb L ∈ unitaryPSPACE O) := by sorry

end KTUnitary.Synth
