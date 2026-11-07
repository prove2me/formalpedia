-- Prove2me | Theorems.Thm_KTUnitary_Synth_corollary_7_16
-- name    : KTUnitary.Synth.corollary_7_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:38:22.307216+00:00
-- url     : https://prove2.me/theorems/8acc998e-2813-49b2-bcf2-a8a4ac5ba3ae
-- title:
--   Corollary 7.16 — EFI pairs relative to $L$ imply $\mathsf{unitaryALL}\neq\mathsf{unitaryP}^{\mathsf{ALL}}$ or $\mathsf{BPP}^L\neq\mathsf{NEXP}^L$
-- statement:
--   Let $L$ be a language for which an EFI pair exists relative to $L$. Then at least one of the following holds:
--   1. $\mathsf{unitaryALL}\neq\mathsf{unitaryP}^{\mathsf{ALL}}$, i.e. the unitary synthesis problem has a negative answer: some unitary language cannot be implemented in polynomial time relative to any classical oracle;
--   2. $\mathsf{BPP}^L\neq\mathsf{NEXP}^L$.
--
--   Here $\mathsf{unitaryALL}$ is the set of all unitary languages and $\mathsf{unitaryP}^{\mathsf{ALL}}$ the unitary languages in $\mathsf{unitaryP}^K$ for some language $K$; $\mathsf{unitaryP}$ asks for time-uniform circuits with FPTEAS gate entries that are $\varepsilon$-close in operator norm to an extension of $U_n$, with $\mathrm{poly}(n,\log1/\varepsilon)$ cost.
--
--   With $L=\emptyset$: proving that computational quantum cryptography exists would require either a negative solution to the unitary synthesis problem or the classical separation $\mathsf{BPP}\neq\mathsf{NEXP}$.
--
--   Differences from the source:
--   - encoding: EFI pair relative to L (Definition 7.13) → EFIPair L: valid time-uniform QCircuit generators whose uniformity machine also prints the output wires, gap 1/(p(n)+1) with p ∈ ℕ[X], security against every non-uniform polynomial-size QCircuit distinguisher; reason: an explicit rendering of Definition 7.13; 1/(p(n)+1) ranges over the same bounds as 1/p(n)
--   - reading: BPP^L, NEXP^L, EXP^L, AM^L (used, not defined) → the standard relativized definitions on the OTM model; reason: the paper relies on the standard definitions
--   - encoding: L used as an oracle → its unitary embedding emb L, with U_0 = 1; reason: "we may sometimes overload L to mean both the language and its unitary embedding" (p. 16); U_0 is not defined in the paper
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
--   - reading: Theorem 1.1 (p. 4): "if quantum commitments exist" → Corollary 7.16: an EFI pair exists relative to L (Nonempty (EFIPair L)); reason: the equivalence of EFI pairs and commitments is cited from [BCQ23; Yan22], not proved; the formal statement in the paper is Corollary 7.16
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Corollary 7.16, p. 39 (informal Theorem 1.1, p. 4)

import Mathlib
import Definitions.Def_KTUnitary_Synth_EFIPair
import Definitions.Def_KTUnitary_Synth_unitaryPALL
import Definitions.Def_KTUnitary_Synth_BPP
import Definitions.Def_KTUnitary_Synth_NEXP

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Corollary 7.16** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Corollary 7.16, p. 39; informal Theorem 1.1, p. 4). Suppose `L` is a
language for which an EFI pair exists relative to `L`. Then at least one of the following holds:
1. `unitaryALL ≠ unitaryP^ALL`, or 2. `BPP^L ≠ NEXP^L`.

**Formalization Note** "An EFI pair exists relative to `L`" is `Nonempty (EFIPair L)`;
`unitaryALL` is `Set.univ : Set ULang` and `unitaryP^ALL` is `unitaryPALL`. Theorem 1.1's "quantum
commitments" are the EFI pairs of Definition 7.13 through the equivalence the paper cites
([BCQ23; Yan22], p. 38). No hypothesis on `L`. -/
theorem corollary_7_16 (L : Oracle) (hEFI : Nonempty (EFIPair L)) :
    (Set.univ : Set ULang) ≠ unitaryPALL ∨ BPP L ≠ NEXP L := by sorry

end KTUnitary.Synth
