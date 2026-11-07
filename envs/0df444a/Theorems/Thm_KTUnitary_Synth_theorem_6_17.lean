-- Prove2me | Theorems.Thm_KTUnitary_Synth_theorem_6_17
-- name    : KTUnitary.Synth.theorem_6_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:37:40.784696+00:00
-- url     : https://prove2.me/theorems/960a9f15-7e1d-485f-8eab-ed9c5a762a5e
-- title:
--   Theorem 6.17 — entrywise characterization of $\mathsf{unitaryPSPACE}$
-- statement:
--   For every unitary language $\mathcal U$ and unitary oracle $\mathcal O$ the following are equivalent:
--   1. $\mathcal U\in\mathsf{unitaryPSPACE}^{\mathcal O}$;
--   2. $\mathcal U\mathrm{EntryPhase}\in\mathsf{unitaryPSPACE}^{\mathcal O}$;
--   3. $\mathcal U\mathrm{Column}\in\mathsf{unitaryPSPACE}^{\mathcal O}$;
--   4. $\mathcal U\mathrm{Entry}$ has an FPUSEAS relative to $\mathcal O$;
--   5. $\mathcal U\mathrm{EntryApx}\in\mathsf{BQUPSPACE}^{\mathcal O}$.
--
--   If $\mathcal O$ is (the unitary embedding of) a language $L$, they are also equivalent to:
--
--   6. $\mathcal U\mathrm{Entry}$ has an FPSEAS relative to $L$;
--   7. $\mathcal U\mathrm{EntryApx}\in\mathsf{PSPACE}^L$.
--
--   Here $\mathcal U\mathrm{Entry}(x,y,b)$ is the real ($b=0$) or imaginary ($b=1$) part of $\langle y|U_n|x\rangle$, $\mathcal U\mathrm{EntryPhase}$ its phase encoding, $\mathcal U\mathrm{EntryApx}$ its approximation promise problem and $\mathcal U\mathrm{Column}$ the column language. All seven items and all directions are stated.
--
--   The theorem says that a unitary is in polynomial space exactly when its entries are, which is what makes the entries of $e^{iA}$ in Theorem 7.14 usable.
--
--   Differences from the source:
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - reading: BQP^𝒪, BQUPSPACE^𝒪, BQPSPACE^L, PSPACE^L → classes of promise problems; a language A is the pair (A, Aᶜ); reason: Definition 4.6 defines the quantum classes on promise problems
--   - encoding: UEntry on {0,1}^{2n+1}, UColumn = {V_{2n+1}} → UEntry is 0 on even lengths and V_m is the identity for even m; reason: the paper defines nothing there; constant values do not change any item
--   - encoding: L used as an oracle → its unitary embedding emb L, with U_0 = 1; reason: "we may sometimes overload L to mean both the language and its unitary embedding" (p. 16); U_0 is not defined in the paper
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structures UCircuit/QCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
--   - reading: a designated output qubit or register of a uniform family → the wire(s) are part of the family: the uniformity machine prints them with the circuit, and a register has distinct wires; reason: Definition 4.5 makes the machine output the family; a wire chosen outside the description would be non-uniform advice (it would decide every unary language), against Definition 4.6 and the proof of Proposition 5.8, which measures a fixed first qubit
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Theorem 6.17, p. 30

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_KTUnitary_Synth_phaseEnc
import Definitions.Def_KTUnitary_Synth_UEntry
import Definitions.Def_KTUnitary_Synth_UColumn
import Definitions.Def_KTUnitary_Synth_FPUSEAS
import Definitions.Def_KTUnitary_Synth_fApx
import Definitions.Def_KTUnitary_Synth_BQUPSPACE
import Definitions.Def_KTUnitary_Synth_HasFPSEAS
import Definitions.Def_KTUnitary_Synth_PromisePSPACE

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **Theorem 6.17** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Theorem 6.17, p. 30; characterization of unitary polynomial space).
The following are equivalent for any unitary language `𝒰` and unitary oracle `𝒪`:
1. `𝒰 ∈ unitaryPSPACE^𝒪`. 2. `𝒰EntryPhase ∈ unitaryPSPACE^𝒪`. 3. `𝒰Column ∈ unitaryPSPACE^𝒪`.
4. `𝒰Entry` has an FPUSEAS relative to `𝒪`. 5. `𝒰EntryApx ∈ BQUPSPACE^𝒪`.
If `𝒪` is additionally a (classical) language `L`, then the above are equivalent to:
6. `𝒰Entry` has an FPSEAS relative to `L`. 7. `𝒰EntryApx ∈ PSPACE^L`.

**Formalization Note** `𝒰EntryPhase = phaseEnc (UEntry 𝒰)`, `𝒰Column = UColumn 𝒰`,
`𝒰EntryApx = fApx (UEntry 𝒰)`. Item 5 uses `BQUPSPACE 𝒪` with the gates of Definition 5.5
(footnote 7, p. 24), and item 7 is `PSPACE^L` on promise problems (`PromisePSPACE L`). In the second
conjunct `𝒪` is the unitary embedding `emb L`. -/
theorem theorem_6_17 :
    (∀ U O : ULang, [U ∈ unitaryPSPACE O, phaseEnc (UEntry U) ∈ unitaryPSPACE O,
      UColumn U ∈ unitaryPSPACE O, FPUSEAS O (UEntry U), fApx (UEntry U) ∈ BQUPSPACE O].TFAE) ∧
    (∀ (U : ULang) (L : Oracle), [U ∈ unitaryPSPACE (emb L),
      phaseEnc (UEntry U) ∈ unitaryPSPACE (emb L), UColumn U ∈ unitaryPSPACE (emb L),
      FPUSEAS (emb L) (UEntry U), fApx (UEntry U) ∈ BQUPSPACE (emb L), HasFPSEAS L (UEntry U),
      fApx (UEntry U) ∈ PromisePSPACE L].TFAE) := by sorry

end KTUnitary.Synth
