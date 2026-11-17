-- Prove2me | Theorems.Thm_KTUnitary_Synth_Supplement_theorem_6_19
-- name    : KTUnitary.Synth.Supplement.theorem_6_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:20:00.535191+00:00
-- url     : https://prove2.me/theorems/4266fa08-1e53-48b4-ae28-3ef5229cc35d
-- title:
--   Theorem 6.19 — erasing garbage in polynomial space: $\mathsf{projUnitaryPSPACE}^L$ is $\mathsf{unitaryPSPACE}^L$ up to global phases
-- statement:
--   For every language $L\subseteq\{0,1\}^*$ and every unitary language $\mathcal U=\{U_n\}_{n\in\mathbb N}$,
--   $$\mathcal U\in\mathsf{projUnitaryPSPACE}^L\iff \exists\,\mathcal V=\{V_n\}\in\mathsf{unitaryPSPACE}^L\ \text{and}\ \{\phi_n\in\mathbb C\}_{n\in\mathbb N}\ \text{with}\ U_n=\phi_nV_n\ \text{for all } n.$$
--
--   Here $L$ is accessed through its unitary embedding $|x,b\rangle\mapsto|x,b\oplus L(x)\rangle$; $\mathsf{unitaryPSPACE}^L$ allows controlled queries, $\mathsf{projUnitaryPSPACE}^L$ does not and only asks for closeness to a dilation.
--
--   The theorem says that global phase is the only obstruction between the two definitions in polynomial space: every unitary implementable with garbage is implementable cleanly after a change of global phase. Theorem 6.23 shows that this fails relative to unitary oracles.
--
--   Differences from the source:
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structure UCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
--   - encoding: L used as an oracle → its unitary embedding emb L, with U_0 = 1; reason: "we may sometimes overload L to mean both the language and its unitary embedding" (p. 16)
--   - encoding: projective L-oracle gates {O_L, O_L*, O_L†, O_L^T} (Definition 5.16) → only uncontrolled O_L gates (published projUnitaryPSPACE L, UCircuit.Plain); reason: O_L = emb L is a real symmetric permutation matrix, so O_L* = O_L† = O_L^T = O_L; same class
--   - encoding: an a-qubit garbage state |g⟩ → any vector g on the a ancilla qubits; reason: for unitary Ū and unitary U_n, Ū|ψ⟩|0^a⟩ = (U_n|ψ⟩)|g⟩ forces ‖g‖ = 1; same instances
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Theorem 6.19, p. 31

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms.Complexity QAdvFew.PoQOracle PSPACEOracleSynth.Main

namespace KTUnitary.Synth.Supplement

/-- **Theorem 6.19** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Theorem 6.19, p. 31; erasing garbage).
"For every language `L`, `𝒰 ∈ projUnitaryPSPACE^L` if and only if there exists a
`𝒱 ∈ unitaryPSPACE^L` and a sequence `{ϕ_n ∈ ℂ}_{n∈ℕ}` such that `U_n = ϕ_n V_n`."

**Formalization Note** `L` is a classical language (`Oracle = Str → Bool`); the projective side is
the published `PSPACEOracleSynth.Main.projUnitaryPSPACE L` (uncontrolled `O_L` gates, which for the
real permutation matrix `O_L` are all four gates `O_L, O_L^*, O_L^†, O_L^T` of Definition 5.16), the
clean side `KTUnitary.Synth.unitaryPSPACE (emb L)`. The phases are arbitrary complex numbers, as
printed; `|ϕ_n| = 1` follows from unitarity and is not assumed. -/
theorem theorem_6_19 (L : Oracle) (U : ULang) :
    U ∈ projUnitaryPSPACE L ↔
      ∃ V ∈ unitaryPSPACE (emb L), ∃ ϕ : ℕ → ℂ, ∀ n : ℕ,
        (U n : Matrix (Bits n) (Bits n) ℂ) = ϕ n • (V n : Matrix (Bits n) (Bits n) ℂ) := by sorry

end KTUnitary.Synth.Supplement
