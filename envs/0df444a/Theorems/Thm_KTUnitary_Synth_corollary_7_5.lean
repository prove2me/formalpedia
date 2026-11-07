-- Prove2me | Theorems.Thm_KTUnitary_Synth_corollary_7_5
-- name    : KTUnitary.Synth.corollary_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:39:15.219179+00:00
-- url     : https://prove2.me/theorems/ffccfb04-4a13-424f-8913-0c4d87f30ed5
-- title:
--   Corollary 7.5 — unitary synthesis puts $\mathsf{unitaryPSPACE}^L$ in $\mathsf{unitaryP}^{\mathsf{FNEXP}^L[\mathrm{poly}]}$
-- statement:
--   If $\mathsf{unitaryALL}=\mathsf{unitaryP}^{\mathsf{ALL}}$, then for every language $L$,
--   $$\mathsf{unitaryPSPACE}^L\subseteq\mathsf{unitaryP}^{\mathsf{FNEXP}^L[\mathrm{poly}]}.$$
--
--   Differences from the source:
--   - reading: the witness y with y_i := W(x, i) → some prefix W(x,0)⋯W(x,ℓ−1) is a witness; the query (x, i) is tup [x, bin i]; reason: the paper leaves the length of y implicit
--   - encoding: L used as an oracle → its unitary embedding emb L, with U_0 = 1; reason: "we may sometimes overload L to mean both the language and its unitary embedding" (p. 16); U_0 is not defined in the paper
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Corollary 7.5, p. 36

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_KTUnitary_Synth_unitaryPALL
import Definitions.Def_KTUnitary_Synth_unitaryPFNEXPpoly

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Corollary 7.5** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Corollary 7.5, p. 36). If `unitaryALL = unitaryP^ALL`, then for any
language `L`, `unitaryPSPACE^L ⊆ unitaryP^{FNEXP^L[poly]}`.

**Formalization Note** `unitaryALL` is `Set.univ : Set ULang`. -/
theorem corollary_7_5 (hall : (Set.univ : Set ULang) = unitaryPALL) (L : Oracle) :
    unitaryPSPACE (emb L) ⊆ unitaryPFNEXPpoly L := by sorry

end KTUnitary.Synth
