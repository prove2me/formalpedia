-- Prove2me | Theorems.Thm_KTUnitary_Synth_lemma_7_4
-- name    : KTUnitary.Synth.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:39:28.700138+00:00
-- url     : https://prove2.me/theorems/5d798640-37e6-4375-a358-750459e16f94
-- title:
--   Lemma 7.4 — the dichotomy for $\mathsf{unitaryPSPACE}^L$
-- statement:
--   For every language $L$ and every $\mathcal U\in\mathsf{unitaryPSPACE}^L$, exactly one of the following holds:
--   1. $\mathcal U\notin\mathsf{unitaryP}^{\mathsf{ALL}}$;
--   2. $\mathcal U\in\mathsf{unitaryP}^{\mathsf{FNEXP}^L[\mathrm{poly}]}$.
--
--   So a unitary language in $\mathsf{unitaryPSPACE}^L$ that is efficiently implementable relative to some oracle is already efficiently implementable relative to witness oracles of an $\mathsf{FNEXP}^L[\mathrm{poly}]$ relation.
--
--   Differences from the source:
--   - reading: either 1 or 2 → Xor' (exactly one holds); reason: "The two items are clearly mutually exclusive" (p. 35)
--   - reading: the witness y with y_i := W(x, i) → some prefix W(x,0)⋯W(x,ℓ−1) is a witness; the query (x, i) is tup [x, bin i]; reason: the paper leaves the length of y implicit
--   - encoding: L used as an oracle → its unitary embedding emb L, with U_0 = 1; reason: "we may sometimes overload L to mean both the language and its unitary embedding" (p. 16); U_0 is not defined in the paper
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.4, p. 34

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_KTUnitary_Synth_unitaryPALL
import Definitions.Def_KTUnitary_Synth_unitaryPFNEXPpoly

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Lemma 7.4** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.4, p. 34; the dichotomy). For every language `L` and every
`𝒰 ∈ unitaryPSPACE^L`, either 1. `𝒰 ∉ unitaryP^ALL`, or 2. `𝒰 ∈ unitaryP^{FNEXP^L[poly]}`.

**Formalization Note** "Either … or" is exclusive: "The two items are clearly mutually exclusive"
(p. 35), so the conclusion is `Xor'`. `unitaryPSPACE^L` is `unitaryPSPACE (emb L)`. -/
theorem lemma_7_4 (L : Oracle) (U : ULang) (hU : U ∈ unitaryPSPACE (emb L)) :
    Xor' (U ∉ unitaryPALL) (U ∈ unitaryPFNEXPpoly L) := by sorry

end KTUnitary.Synth
