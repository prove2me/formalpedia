-- Prove2me | Theorems.Thm_KTUnitary_Synth_corollary_7_11
-- name    : KTUnitary.Synth.corollary_7_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:37:19.763691+00:00
-- url     : https://prove2.me/theorems/535b2772-484b-401e-aa67-04c9cfa9ad66
-- title:
--   Corollary 7.11 — separating $\mathsf{unitaryP}^L$ from $\mathsf{unitaryPSPACE}^L$ is hard
-- statement:
--   If $L$ is a language with $\mathsf{unitaryP}^L\neq\mathsf{unitaryPSPACE}^L$, then at least one of the following holds:
--   1. $\mathsf{unitaryP}^{\mathsf{ALL}}\neq\mathsf{unitaryALL}$;
--   2. $\mathsf{BPP}^L\neq\mathsf{NEXP}^L$.
--
--   Differences from the source:
--   - reading: BPP^L, NEXP^L, EXP^L, AM^L (used, not defined) → the standard relativized definitions on the OTM model; reason: the paper relies on the standard definitions
--   - encoding: L used as an oracle → its unitary embedding emb L, with U_0 = 1; reason: "we may sometimes overload L to mean both the language and its unitary embedding" (p. 16); U_0 is not defined in the paper
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Corollary 7.11, p. 37

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_KTUnitary_Synth_unitaryPALL
import Definitions.Def_KTUnitary_Synth_BPP
import Definitions.Def_KTUnitary_Synth_NEXP

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Corollary 7.11** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Corollary 7.11, p. 37). If there is a language `L` relative to which
`unitaryP^L ≠ unitaryPSPACE^L`, then at least one of the following holds:
1. `unitaryP^ALL ≠ unitaryALL`, or 2. `BPP^L ≠ NEXP^L`.

**Formalization Note** Stated for every `L`: the hypothesis is about `L`, and so is the second
alternative. `unitaryALL = Set.univ`; `unitaryP^L = unitaryP (emb L)`. -/
theorem corollary_7_11 (L : Oracle) (hsep : unitaryP (emb L) ≠ unitaryPSPACE (emb L)) :
    unitaryPALL ≠ Set.univ ∨ BPP L ≠ NEXP L := by sorry

end KTUnitary.Synth
