-- Prove2me | Theorems.Thm_KTUnitary_Synth_lemma_7_7
-- name    : KTUnitary.Synth.lemma_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:33:53.432524+00:00
-- url     : https://prove2.me/theorems/6bd887e2-20ac-4ff4-bff8-8232a2f68154
-- title:
--   Lemma 7.7 — easy witness lemma, relativized
-- statement:
--   Let $L$ be a language with $\mathsf{AM}^L=\mathsf{NEXP}^L$. Then every relation $R\in\mathsf{FNEXP}^L$ has a witness oracle in $\mathsf{EXP}^L$: there is a language $W\in\mathsf{EXP}^L$ such that for every $x$ that has a witness, the bits $W(x,0),W(x,1),\dots$ spell one.
--
--   This is the easy witness lemma of Impagliazzo, Kabanets and Wigderson, in the relativized form the paper uses.
--
--   Differences from the source:
--   - reading: the witness y with y_i := W(x, i) → some prefix W(x,0)⋯W(x,ℓ−1) is a witness; the query (x, i) is tup [x, bin i]; reason: the paper leaves the length of y implicit
--   - reading: BPP^L, NEXP^L, EXP^L, AM^L (used, not defined) → the standard relativized definitions on the OTM model; reason: the paper relies on the standard definitions
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.7, p. 37 ([IKW02, Theorem 29])

import Mathlib
import Definitions.Def_KTUnitary_Synth_AM
import Definitions.Def_KTUnitary_Synth_NEXP
import Definitions.Def_KTUnitary_Synth_EXP
import Definitions.Def_KTUnitary_Synth_FNEXP
import Definitions.Def_KTUnitary_Synth_IsWitnessOracle

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Lemma 7.7** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.7, p. 37; easy witness lemma [IKW02, Theorem 29]). Suppose `L`
is a language for which `AM^L = NEXP^L`. Then every relation `R ∈ FNEXP^L` has a witness oracle in
`EXP^L`.

**Formalization Note** A witness oracle in `EXP^L` is a language `W` (an `Oracle`) with
`{s | W s} ∈ EXP L` and `IsWitnessOracle W R`. The lemma is cited by the paper, relativized. -/
theorem lemma_7_7 (L : Oracle) (hAM : AM L = NEXP L) (R : Set (Str × Str)) (hR : R ∈ FNEXP L) :
    ∃ W : Oracle, {s | W s = true} ∈ EXP L ∧ IsWitnessOracle W R := by sorry

end KTUnitary.Synth
