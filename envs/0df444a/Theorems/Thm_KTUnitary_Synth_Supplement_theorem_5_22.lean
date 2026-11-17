-- Prove2me | Theorems.Thm_KTUnitary_Synth_Supplement_theorem_5_22
-- name    : KTUnitary.Synth.Supplement.theorem_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:18:43.561086+00:00
-- url     : https://prove2.me/theorems/b79cf57f-ac40-4188-a867-a4d401132bdf
-- title:
--   Theorem 5.22 — $\mathcal U\in\mathsf{unitaryK}$ iff $c\mathcal U\in\mathsf{projUnitaryK}$
-- statement:
--   Let $\mathsf K\in\{\mathsf P,\mathsf{PSPACE}\}$. For every unitary language $\mathcal U=\{U_n\}_{n\in\mathbb N}$,
--   $$\mathcal U\in\mathsf{unitaryK}\iff c\,\mathcal U\in\mathsf{projUnitaryK},$$
--   where $c\,\mathcal U$ is the unitary language with member $cU_n=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes U_n$ on $n+1$ qubits.
--
--   Here $\mathsf{unitaryK}$ (Definition 5.2) asks for a uniform family of circuits on $n+a$ qubits, $a\le\mathrm{poly}(n,\log1/\varepsilon)$, whose operator-norm distance to some **extension** of $U_n$ (a unitary $\overline U$ with $\overline U|\psi\rangle|0^a\rangle=(U_n|\psi\rangle)|0^a\rangle$) is at most $\varepsilon$; $\mathsf{projUnitaryK}$ (Definition 5.12) asks the same with a **dilation** (a unitary with $\overline U|\psi\rangle|0^a\rangle=(U_n|\psi\rangle)|g\rangle$ for one garbage state $|g\rangle$). For $\mathsf K=\mathsf P$ the family is time-uniform, for $\mathsf K=\mathsf{PSPACE}$ space-uniform. Both values of $\mathsf K$ and both directions are stated.
--
--   With Theorems 5.20 and 5.21 it shows that the clean and projective classes each embed into the other, so every statement about one class has an equivalent reformulation about the other.
--
--   Differences from the source:
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structure UCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
--   - encoding: the unrelativized classes unitaryK and projUnitaryK → the classes relative to the empty language ∅ = fun _ => false: unitaryK(emb ∅) and projUnitaryK(∅); reason: emb ∅ is the identity on every number of qubits (proved in the verification file), so its oracle gates are identities and the classes are the oracle-free ones of Definitions 5.2 and 5.12
--   - encoding: an a-qubit garbage state |g⟩ → any vector g on the a ancilla qubits; reason: for unitary Ū and unitary U_n, Ū|ψ⟩|0^a⟩ = (U_n|ψ⟩)|g⟩ forces ‖g‖ = 1; same instances
--   - encoding: c𝒰 = {cU_n}_{n∈ℕ} → member cU_n on n + 1 qubits with the control on the first wire, and the 1 × 1 identity on 0 qubits; reason: the paper does not fix the control wire or a member on 0 qubits; circuits act on arbitrary wires and the 0-qubit identity is in every class
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Theorem 5.22, p. 23

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_PSPACEOracleSynth_Main_Dilation
import Definitions.Def_KTUnitary_Synth_Supplement_ctrlLang

open QAlgorithms.Complexity QAdvFew.PoQOracle PSPACEOracleSynth.Main

namespace KTUnitary.Synth.Supplement

/-- **Theorem 5.22** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Theorem 5.22, p. 23).
"Let `K ∈ {P, PSPACE}`. Then `𝒰 ∈ unitaryK` if and only if `c𝒰 ∈ projUnitaryK`."

Here `c𝒰` is `ctrlLang 𝒰` (member `cU_n` on `n + 1` qubits, control on the first wire; the
`1 × 1` identity on `0` qubits).

**Formalization Note** The unrelativized classes are the classes relative to the empty language
`∅ = fun _ => false`: `unitaryK = unitaryK^{emb ∅}` (published `KTUnitary.Synth.unitaryP`/`unitaryPSPACE`)
and `projUnitaryK = projUnitaryK^∅` (published `PSPACEOracleSynth.Main.projUnitaryP`/`projUnitaryPSPACE`).
`emb ∅` is the identity on every number of qubits, so every oracle gate is an identity and these
are the oracle-free classes of Definitions 5.2 and 5.12. `ε = 2^{−l}` (footnote 4, p. 14). Both
`K = P` and `K = PSPACE` are stated, as a conjunction. -/
theorem theorem_5_22 :
    (∀ U : ULang, U ∈ unitaryP (emb (fun _ : Str => false)) ↔
      ctrlLang U ∈ projUnitaryP (fun _ : Str => false)) ∧
    (∀ U : ULang, U ∈ unitaryPSPACE (emb (fun _ : Str => false)) ↔
      ctrlLang U ∈ projUnitaryPSPACE (fun _ : Str => false)) := by sorry

end KTUnitary.Synth.Supplement
