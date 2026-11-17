-- Prove2me | Theorems.Thm_KTUnitary_Synth_Supplement_theorem_6_23
-- name    : KTUnitary.Synth.Supplement.theorem_6_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:20:38.294138+00:00
-- url     : https://prove2.me/theorems/9a4381ac-11e5-4bc2-9ae4-de3961722b3b
-- title:
--   Theorem 6.23 — relative to $\mathcal U\otimes\mathcal U^\dagger$, no rephasing of $\mathcal U$ is in $\mathsf{unitaryPSPACE}$
-- statement:
--   There is a unitary language $\mathcal U=\{U_n\}_{n\in\mathbb N}$ such that for every unitary language $\mathcal V=\{\phi_nU_n\}_{n\in\mathbb N}$ that equals $\mathcal U$ up to a sequence of global phases $\{\phi_n\}$,
--   $$\mathcal V\notin\mathsf{unitaryPSPACE}^{\mathcal U\otimes\mathcal U^\dagger}.$$
--
--   The oracle $\mathcal U\otimes\mathcal U^\dagger$ has member $U_n\otimes U_n^\dagger$ on $2n$ qubits and is queried with all eight oracle gates of Definition 5.5. Since $\mathcal U\in\mathsf{projUnitaryPSPACE}^{\mathcal U\otimes\mathcal U^\dagger}$, the theorem shows that Theorem 6.19 does not relativize to unitary oracles.
--
--   Differences from the source:
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, passed in unary as 1^l; reason: footnote 4, p. 14 assumes ε = 2^{−λ} without loss of generality
--   - reading: "an FPTEAS encoding f" of the gates → one encoding f per circuit family, fixed for all n and ε; reason: Definition 4.2 speaks of a single encoding; the family's machine must output finitely described gates
--   - encoding: a polynomial-space machine with a write-only output tape prints the circuit → the description has length ≤ 2^{poly}, every gate description has polynomial length, and its bits form a PSPACE language; reason: equivalent: count output bits to answer a bit query, or print bit after bit
--   - encoding: Turing machines and quantum circuits with FPTEAS-encoded gates → the published OTM model and the circuit structure UCircuit with explicit descriptions over Bits n; reason: an explicit model of the conventions of §4; same classes
--   - encoding: 𝒰 ⊗ 𝒰† = {U_n ⊗ U_n†}_{n∈ℕ} → the unitary language with member U_n ⊗ U_n† on 2n qubits (U_n on the first n wires) and the identity on an odd number of qubits; reason: a unitary language has a member on every number of qubits; identities are in every class, and poly(2n, log 1/ε) = poly(n, log 1/ε)
--   - encoding: a sequence of global phases {ϕ_n} → any sequence ϕ : ℕ → ℂ with V_n = ϕ_n U_n as matrices; reason: for unitary U_n and V_n, V_n = ϕ_n U_n forces |ϕ_n| = 1; same instances
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Theorem 6.23, p. 33

import Mathlib
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms.Complexity QAdvFew.PoQOracle PSPACEOracleSynth.Main

namespace KTUnitary.Synth.Supplement

/-- **Theorem 6.23** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Theorem 6.23, p. 33).
"There is a unitary language `𝒰` such that for every unitary language `𝒱 = {ϕ_n U_n}_{n∈ℕ}` that
equals `𝒰` up to a sequence of global phases `{ϕ_n}_{n∈ℕ}`, we have `𝒱 ∉ unitaryPSPACE^{𝒰⊗𝒰†}`."

**Formalization Note** The oracle is the unitary language `𝒰 ⊗ 𝒰† = tensorAdj 𝒰` (published
`PSPACEOracleSynth.Main.tensorAdj`, identity on an odd number of qubits), with all eight oracle gates
of Definition 5.5. The phases are arbitrary complex numbers (`|ϕ_n| = 1` follows from unitarity of
`V_n` and `U_n`). The existential over `𝒰` comes first. -/
theorem theorem_6_23 :
    ∃ U : ULang, ∀ V : ULang,
      (∃ ϕ : ℕ → ℂ, ∀ n : ℕ,
        (V n : Matrix (Bits n) (Bits n) ℂ) = ϕ n • (U n : Matrix (Bits n) (Bits n) ℂ)) →
      V ∉ unitaryPSPACE (tensorAdj U) := by sorry

end KTUnitary.Synth.Supplement
