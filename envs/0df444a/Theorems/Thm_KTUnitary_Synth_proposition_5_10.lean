-- Prove2me | Theorems.Thm_KTUnitary_Synth_proposition_5_10
-- name    : KTUnitary.Synth.proposition_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:34:43.476819+00:00
-- url     : https://prove2.me/theorems/e39971e8-796a-42dc-97f5-bbc3bf038153
-- title:
--   Proposition 5.10 — unitary classes are self-low
-- statement:
--   For every unitary oracle $\mathcal O$ and $\mathsf K\in\{\mathsf P,\mathsf{PSPACE}\}$,
--   $$\mathsf{unitaryK}^{\mathsf{unitaryK}^{\mathcal O}}=\mathsf{unitaryK}^{\mathcal O},$$
--   where $\mathsf{unitaryK}^{\mathsf{unitaryK}^{\mathcal O}}=\bigcup_{\mathcal V\in\mathsf{unitaryK}^{\mathcal O}}\mathsf{unitaryK}^{\mathcal V}$. Both equalities ($\mathsf K=\mathsf P$ and $\mathsf K=\mathsf{PSPACE}$) are stated.
--
--   Self-lowness lets a unitary algorithm call another one of the same class as an exact oracle, which the later proofs use repeatedly.
--
--   Differences from the source:
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Proposition 5.10, p. 19

import Mathlib
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Proposition 5.10** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Proposition 5.10, p. 19; unitary classes are self-low). Let
`K ∈ {P, PSPACE}`. Then `unitaryK^{unitaryK^𝒪} = unitaryK^𝒪`.

**Formalization Note** `unitaryK^{unitaryK^𝒪}` is the union of `unitaryK^𝒱` over the unitary
languages `𝒱 ∈ unitaryK^𝒪`. Both values of `K` and both inclusions are stated, for every unitary
oracle `𝒪`. -/
theorem proposition_5_10 (O : ULang) :
    (⋃ V ∈ unitaryP O, unitaryP V) = unitaryP O ∧
    (⋃ V ∈ unitaryPSPACE O, unitaryPSPACE V) = unitaryPSPACE O := by sorry

end KTUnitary.Synth
