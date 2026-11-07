-- Prove2me | Theorems.Thm_KTUnitary_Synth_theorem_7_14
-- name    : KTUnitary.Synth.theorem_7_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:38:08.818667+00:00
-- url     : https://prove2.me/theorems/5659587a-61ce-44f0-a096-1cda0ac66abf
-- title:
--   Theorem 7.14 — EFI pairs separate $\mathsf{unitaryP}^L$ from $\mathsf{unitaryPSPACE}^L$
-- statement:
--   If an EFI pair exists relative to a language $L$, then
--   $$\mathsf{unitaryP}^L\neq\mathsf{unitaryPSPACE}^L .$$
--
--   An EFI pair is a pair of efficiently generated mixed states that are statistically far but computationally indistinguishable; a polynomial-space unitary (phase estimation on $e^{i(\rho_0-\rho_1)}$) distinguishes them, so it cannot be implemented in polynomial time.
--
--   Differences from the source:
--   - encoding: EFI pair relative to L (Definition 7.13) → EFIPair L: valid time-uniform QCircuit generators whose uniformity machine also prints the output wires, gap 1/(p(n)+1) with p ∈ ℕ[X], security against every non-uniform polynomial-size QCircuit distinguisher; reason: an explicit rendering of Definition 7.13; 1/(p(n)+1) ranges over the same bounds as 1/p(n)
--   - encoding: L used as an oracle → its unitary embedding emb L, with U_0 = 1; reason: "we may sometimes overload L to mean both the language and its unitary embedding" (p. 16); U_0 is not defined in the paper
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Theorem 7.14, p. 38

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_KTUnitary_Synth_EFIPair

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Theorem 7.14** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Theorem 7.14, p. 38). If EFI pairs exist relative to a language `L`,
then `unitaryP^L ≠ unitaryPSPACE^L`.

**Formalization Note** "EFI pairs exist relative to `L`" is `Nonempty (EFIPair L)`. -/
theorem theorem_7_14 (L : Oracle) (hEFI : Nonempty (EFIPair L)) :
    unitaryP (emb L) ≠ unitaryPSPACE (emb L) := by sorry

end KTUnitary.Synth
