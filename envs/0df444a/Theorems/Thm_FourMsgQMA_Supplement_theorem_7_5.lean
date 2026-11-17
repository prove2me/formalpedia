-- Prove2me | Theorems.Thm_FourMsgQMA_Supplement_theorem_7_5
-- name    : FourMsgQMA.Supplement.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:36:24.600559+00:00
-- url     : https://prove2.me/theorems/9bc096eb-558b-4c55-8f82-368488c3b88a
-- title:
--   Theorem 7.5 — six-message succinct arguments for QMA from LWE
-- statement:
--   This is Theorem 7.5 (six-message succinct QMA from LWE) in the pinned-down version requested by the operator.
--
--   Fix $\varepsilon\in(0,1)$ and assume:
--
--   1. $\mathrm{Hyp}(\varepsilon)$;
--   2. an efficient hash family that is collapsing and collision resistant, such that for every efficiently computable relation there is an efficient complete PCP for which Kilian's argument over that hash has guaranteed extraction (Definition 3.25);
--   3. a leveled FHE scheme as in §3.9 (uniform, compact, with shallow decryption, uniformly correct and IND-CPA secure);
--   4. post-quantum PRFs (Definition 3.30) for every polynomial domain and output length.
--
--   Then every QMA promise problem $L$ with verification family $F$ has a **six-message classical-verifier argument** that is uniform, **public-coin except for its first message**, complete with error $\mathrm{negl}(\lambda)$ for $N(\lambda,T)$ copies of any witness in $W_Q(x,2/3)$, selectively sound (Definition 3.4) with error
--   $$
--   1-\frac{1}{128\lambda^4}+\mathrm{negl}(\lambda),
--   $$
--   has every message and the work of every verifier stage at most $p(\lambda,|x|,\log(T+1))$, and uses polynomially many witness copies.
--
--   This is the construction before outer amplification (Section 8); it is a fully succinct six-message argument for all of QMA from LWE-type assumptions.
--
--   Differences from the source:
--   - reading: "quantum-secure LWE at parameters sufficient for Theorem 7.1" → Hyp(ε) for the given ε ∈ (0, 1); reason: the same reading as Theorem 7.1 and the published corollary_5_15
--   - reading: "collapsing hashes" and "With Kilian guaranteed extraction as in Definition 3.25" → ∃ H efficient, collapsing and collision resistant such that for every efficient relation R there is an efficient complete PCP P with (Kilian.mk H P).GuaranteedExtraction R; reason: §7.3 (p.53) uses "collapsing H (also collision resistant), independently keyed collision-resistant G … and Kilian's argument Σ with guaranteed extraction" for the relation R_c
--   - reading: "leveled classical FHE with uniform correctness" → ∃ FHE with IsUniform, Compact, ShallowDec, UniformlyCorrect and INDCPA (published FourMsgQMA.FHE); reason: §3.9 specification referenced by §7.3; Construction 7.4 encrypts r and decrypts with SK
--   - reading: "the PRFs above" → for every polynomial domain length ℓ and output length v an efficient PRF secure in the sense of Definition 3.30; reason: §7.1 uses one-bit PRFs for the basis generator and domain-separated PRF outputs for the private final coins (pp.50–51)
--   - reading: "Construction 7.4 is public-coin except for its first message, has completeness …, selective soundness …" → ∃ an Arg6 with IsUniform, PublicCoinAfterFirst, Complete, Sound with s(λ) = 1 − 1/(128λ⁴), Succinct and CopiesPoly (pinned-down existential version); reason: Construction 7.4 rests on the [GKNV25] commitment and the [ACGH20] test, which this paper does not reproduce
--   - encoding: "Every message and the total verifier work have complexity poly(λ, |x|, log T)" → Arg6.Succinct: one polynomial p; every message, every honest answer and the work of each of Pre, V1, V2, V3, Dec on the inputs that occur ≤ p(λ, |x|, ⌈log₂(T+1)⌉); longer answers rejected; reason: §3.3 general-QMA succinctness (p.12); §7.4: "This accounts for total verifier work, including the first message"
--   - encoding: 1 − 1/(128λ⁴) + negl(λ) → 1 − (128 (λ : ℝ)^4)⁻¹ + ν(λ), which is 1 + ν(0) at λ = 0; reason: Lean division convention; a single trivial point; = 1 − g²/128 with g = λ^{-2} (p.55)
--   - encoding: QPT adversaries, honest prover, witness copies, T → IsQPT strategies; a uniformly generated honest quantum core with N(λ, T) copies of ρ ∈ W_Q(x, 2/3); T = t_L(x); reason: pinned-down model of the base mission
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Theorem 7.5, p.53 (PDF 55); Construction 7.4, pp.52–53 (PDF 54–55); §7.4, p.53

import Mathlib
import Definitions.Def_FourMsgQMA_LWEHyp
import Definitions.Def_FourMsgQMA_FHE
import Definitions.Def_FourMsgQMA_Supplement_GuaranteedExtraction
import Definitions.Def_FourMsgQMA_Supplement_PRF
import Definitions.Def_FourMsgQMA_Supplement_Arg6

namespace FourMsgQMA

namespace Supplement

open QAlgorithms.Complexity TightPQRepetition.Main

/-- **Theorem 7.5** (Six-message succinct QMA from LWE), Goyal, Koppula, STOC 2027 submission
(sha256 6c523d45…), p.53 (PDF 55), pinned-down version (operator request): "Assume quantum-secure LWE
at parameters sufficient for Theorem 7.1, collapsing hashes, leveled classical FHE with uniform
correctness, and the PRFs above. With Kilian guaranteed extraction as in Definition 3.25,
Construction 7.4 is public-coin except for its first message, has completeness `1 − negl(λ)`, and
has selective soundness at most `1 − 1/(128λ⁴) + negl(λ)`. Every message and the total verifier work
have complexity `poly(λ, |x|, log T)`. The honest prover uses polynomially many witness copies."

Fix `ε ∈ (0, 1)` and assume:

1. `Hyp(ε)`;
2. an efficient hash family that is collapsing and collision resistant, such that for every
   efficiently computable bounded relation there is an efficient complete PCP for which Kilian's
   argument over that hash has guaranteed extraction (Definition 3.25);
3. a leveled FHE scheme as specified in §3.9 (uniform, compact, shallow decryption, uniform
   correctness, post-quantum IND-CPA);
4. post-quantum PRFs (Definition 3.30) for every polynomial domain and output length.

Then every QMA promise problem `L` with verification family `F` has a six-message argument that is
uniform, public-coin except for its first message, complete with error `negl(λ)` for `N(λ, T)` copies
of any witness in `W_Q(x, 2/3)`, selectively sound with error `1 − 1/(128λ⁴) + negl(λ)`, has every
message and the work of every verifier stage at most `p(λ, |x|, ⌈log₂(T + 1)⌉)`, and uses
polynomially many witness copies.

**Formalization Note** The LWE assumption is read as `Hyp(ε)`; `T = t_L(x)`; `1/(128λ⁴)` is
`(128 λ⁴)⁻¹`, which Lean evaluates to `0` at `λ = 0` (a single trivial point). -/
theorem theorem_7_5 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hLWE : LWEHyp ε)
    (hHash : ∃ H : HashFamily, H.Efficient ∧ H.Collapsing ∧ H.CollisionResistant ∧
      ∀ R : Relation, R.Efficient →
        ∃ P : PCP, P.Efficient ∧ P.Complete R ∧ (Kilian.mk H P).GuaranteedExtraction R)
    (hFHE : ∃ E : FHE, E.IsUniform ∧ E.Compact ∧ E.ShallowDec ∧ E.UniformlyCorrect ∧ E.INDCPA)
    (hPRF : ∀ l v : ℕ → ℕ, PolyBound l → PolyBound v →
      ∃ Φ : PRF, Φ.Efficient l v ∧ Φ.Secure l v)
    (L : PromiseProblem) (F : QMAFamily) (hLF : IsQMAVerifierFor L F) :
    ∃ A : Arg6, A.IsUniform ∧ A.PublicCoinAfterFirst ∧ A.Complete L F ∧
      A.Sound L F (fun lam => 1 - (128 * (lam : ℝ) ^ 4)⁻¹) ∧ A.Succinct F ∧ A.CopiesPoly := by sorry

end Supplement

end FourMsgQMA
