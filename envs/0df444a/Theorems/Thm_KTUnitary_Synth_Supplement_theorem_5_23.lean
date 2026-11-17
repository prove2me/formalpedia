-- Prove2me | Theorems.Thm_KTUnitary_Synth_Supplement_theorem_5_23
-- name    : KTUnitary.Synth.Supplement.theorem_5_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:19:27.620483+00:00
-- url     : https://prove2.me/theorems/1630029e-907a-4ab0-8b13-c08030ad9de4
-- title:
--   Theorem 5.23 — $\mathcal U\in\mathsf{projUnitaryK}^{\mathcal O}$ iff $\mathcal U\otimes\mathcal U^\dagger\in\mathsf{unitaryK}^{\mathcal O\otimes\mathcal O^\dagger}$
-- statement:
--   Let $\mathsf K\in\{\mathsf P,\mathsf{PSPACE}\}$. For every unitary oracle $\mathcal O=\{O_n\}$ and every unitary language $\mathcal U=\{U_n\}$,
--   $$\mathcal U\in\mathsf{projUnitaryK}^{\mathcal O}\iff \mathcal U\otimes\mathcal U^\dagger\in\mathsf{unitaryK}^{\mathcal O\otimes\mathcal O^\dagger}.$$
--
--   On the left, the circuits are projective $\mathcal O$-oracle circuits (Definition 5.16: oracle gates $O_n,O_n^*,O_n^\dagger,O_n^{\mathrm T}$, no controlled queries) and must be close to a dilation of $U_n$. On the right, the circuits are $(\mathcal O\otimes\mathcal O^\dagger)$-oracle circuits in the sense of Definition 5.5 (all eight gates, including controlled ones), with oracle member $O_n\otimes O_n^\dagger$ on $2n$ qubits, and must be close to an extension of $U_n\otimes U_n^\dagger$. Both values of $\mathsf K$ and both directions are stated.
--
--   This is the relativized form of Theorem 5.20; it gives the self-lowness of the projective classes (Proposition 5.19) and is the first step of Theorem 6.19.
--
--   Differences from the source:
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structure UCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
--   - encoding: an a-qubit garbage state |g⟩ → any vector g on the a ancilla qubits; reason: for unitary Ū and unitary U_n, Ū|ψ⟩|0^a⟩ = (U_n|ψ⟩)|g⟩ forces ‖g‖ = 1; same instances
--   - encoding: 𝒰 ⊗ 𝒰† = {U_n ⊗ U_n†}_{n∈ℕ} → the unitary language with member U_n ⊗ U_n† on 2n qubits (U_n on the first n wires) and the identity on an odd number of qubits; reason: a unitary language has a member on every number of qubits; identities are in every class, and poly(2n, log 1/ε) = poly(n, log 1/ε)
--   - encoding: the unitary oracle 𝒪 ⊗ 𝒪† → the unitary language tensorAdj 𝒪 (member O_n ⊗ O_n† on 2n qubits, identity on an odd number of qubits); reason: an oracle gate on an odd number of qubits is then an identity, which any circuit can omit
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Theorem 5.23, p. 23

import Mathlib
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_PSPACEOracleSynth_Main_Dilation
import Definitions.Def_KTUnitary_Synth_Supplement_projUnitaryPU
import Definitions.Def_KTUnitary_Synth_Supplement_projUnitaryPSPACEU

open QAlgorithms.Complexity QAdvFew.PoQOracle PSPACEOracleSynth.Main

namespace KTUnitary.Synth.Supplement

/-- **Theorem 5.23** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Theorem 5.23, p. 23).
"Let `K ∈ {P, PSPACE}`. Then `𝒰 ∈ projUnitaryK^𝒪` if and only if `𝒰 ⊗ 𝒰† ∈ unitaryK^{𝒪⊗𝒪†}`."

For every unitary oracle `𝒪` and every unitary language `𝒰`: the left side is the projective class
relative to `𝒪` (`projUnitaryPU 𝒪`/`projUnitaryPSPACEU 𝒪`: oracle gates `O_n, O_n^*, O_n^†, O_n^T`,
no controlled queries, Definitions 5.16–5.17), the right side the clean class (published
`KTUnitary.Synth.unitaryP`/`unitaryPSPACE`, all eight oracle gates of Definition 5.5) relative to the
unitary oracle `𝒪 ⊗ 𝒪† = tensorAdj 𝒪`.

**Formalization Note** `𝒰 ⊗ 𝒰†` and `𝒪 ⊗ 𝒪†` are the published `PSPACEOracleSynth.Main.tensorAdj`
(identity on an odd number of qubits). `ε = 2^{−l}` (footnote 4, p. 14). Both `K = P` and
`K = PSPACE` are stated, as a conjunction. -/
theorem theorem_5_23 :
    (∀ O U : ULang, U ∈ projUnitaryPU O ↔ tensorAdj U ∈ unitaryP (tensorAdj O)) ∧
    (∀ O U : ULang, U ∈ projUnitaryPSPACEU O ↔
      tensorAdj U ∈ unitaryPSPACE (tensorAdj O)) := by sorry

end KTUnitary.Synth.Supplement
