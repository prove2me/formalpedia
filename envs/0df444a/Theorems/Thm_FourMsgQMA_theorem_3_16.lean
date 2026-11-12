-- Prove2me | Theorems.Thm_FourMsgQMA_theorem_3_16
-- name    : FourMsgQMA.theorem_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:34:42.442206+00:00
-- url     : https://prove2.me/theorems/3c3edd9a-b368-4627-81d4-7f58e67bde9e
-- title:
--   Theorem 3.16 — leveled FHE from LWE
-- statement:
--   This is Theorem 3.16 (leveled FHE from LWE, [GSW13]) in the pinned-down version requested by the operator.
--
--   Fix $\varepsilon\in(0,1)$ and assume $\mathrm{Hyp}(\varepsilon)$. Then there is one leveled FHE scheme $\mathrm{FHE}=(\mathrm{Gen},\mathrm{Enc},\mathrm{Eval},\mathrm{Dec})$, with $\mathrm{Gen}$ taking $1^L$, that has all of the following properties:
--
--   1. polynomial-time algorithms and the compactness of §3.9 (keys, fresh and evaluated ciphertexts of length $\mathrm{poly}(\lambda,L)$);
--   2. uniform correctness (Definition 3.14) for all polynomial bounds on the depth, the number of inputs and the circuit size;
--   3. post-quantum IND-CPA security (Definition 3.15) for every polynomial depth bound;
--   4. a total decryption circuit of depth $\mathrm{polylog}(\lambda+L)$, including on malformed inputs:
--   $$
--   \exists c\ \forall\lambda,L:\quad \operatorname{depth}(\mathrm{Dec})\le c\,\lceil\log_2(\lambda+L+2)\rceil^{c}.
--   $$
--
--   The scheme encrypts the chain of secret keys and the base verifier's private state in the construction of §5.1. Its shallow decryption is what keeps the encrypted AND tree evaluable at polynomial depth.
--
--   Differences from the source:
--   - reading: "suitable post-quantum LWE parameters" → Hyp(ε) for the given ε ∈ (0,1): LWE (Assumption 3.10's game) for every efficiently computable (n, q, σ) with polynomial n ≥ max(λ,1), 2 ≤ q ≤ 2^{n^ε}, discrete Gaussian error D_{ℤ,σ} with σ ≥ 2√n; reason: the paper fixes no family ("Each instantiation specifies its family", p.15); it keeps a superpolynomial modulus-to-noise ratio (p.14) and GSW needs q > 8(M+1)^L B with dimension and log q polynomial (p.18), i.e. ratio 2^{poly}; σ ≥ 2√n is Regev's regime
--   - reading: "For every polynomial depth bound L, suitable post-quantum LWE parameters give a leveled FHE scheme" → one scheme, whose key generation takes 1^L, with correctness and IND-CPA security for every polynomial depth bound; reason: the syntax of §3.9 has Gen(1^λ, 1^L) and compactness poly(λ, L); this is the stronger of the two readings
--   - reading: depth polylog(λ + L) → ∃ c, depth ≤ c·⌈log₂(λ+L+2)⌉^c, by one NAND circuit for each (λ, L, secret-key length, ciphertext length), chosen before the key and correct for every key in the support; reason: standard meaning of polylog; +2 avoids log 0 and log 1
--   - reading: PPT / deterministic classical algorithms and their running times → QAlgorithms.Complexity.PolyTimeComputable maps of the packed inputs with explicit uniform coins; per-instance work as Boolean circuit size (ComputedOn); reason: the paper's machine model is informal (§3.3); this is the standard uniform model
--   - encoding: QPT adversaries and distinguishers: nonuniform polynomial-size quantum circuit families with one quantum advice state (§3.1, p.9) → the published TightPQRepetition.Main.IsQPT strategies and IsQTestFamily distinguishers (gate set: all one- and two-qubit unitaries), on both sides of the implication; reason: a finite universal gate set approximates these circuits to negligible error at polynomial cost (Solovay–Kitaev), so the classes give the same negligible-advantage statements
--   - encoding: the IND-CPA game of Definition 3.15 with classical bits µ₀, µ₁ and guess b̂ → a two-round Verifier carrier: the adversary's first answer's first two bits are (µ₀, µ₁), its second answer's first bit is b̂; reason: parsing convention; every adversary of the source is one of these
--   - encoding: Boolean circuits over the fan-in-two NAND basis → NandCircuit (topologically ordered gate list, last wire is the output); reason: Lean representation; same circuits
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Theorem 3.16, p.18 (PDF 20)

import Mathlib
import Definitions.Def_FourMsgQMA_LWEHyp
import Definitions.Def_FourMsgQMA_FHE

namespace FourMsgQMA

/-- **Theorem 3.16** (Leveled FHE from LWE [GSW13]), Goyal, Koppula, STOC 2027 submission
(sha256 6c523d45…), p.18 (PDF 20), pinned-down version (operator request).

For every `ε ∈ (0, 1)`, under `Hyp(ε)` there is a leveled FHE scheme, uniform in the depth bound
`L` (its key generation takes `1^L`), with polynomial-time algorithms and the compactness of §3.9,
uniform correctness (Definition 3.14) for every polynomial depth bound, post-quantum IND-CPA
security (Definition 3.15) for every polynomial depth bound, and a total decryption circuit of depth
`polylog(λ + L)` on all inputs.

**Formalization Note** "suitable post-quantum LWE parameters" is read as `Hyp(ε)`; one scheme
serves every polynomial depth bound. -/
theorem theorem_3_16 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hLWE : LWEHyp ε) :
    ∃ E : FHE, E.IsUniform ∧ E.Compact ∧ E.UniformlyCorrect ∧ E.INDCPA ∧ E.ShallowDec := by sorry

end FourMsgQMA
