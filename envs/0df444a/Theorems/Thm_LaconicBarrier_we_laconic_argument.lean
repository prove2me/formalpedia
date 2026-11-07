-- Prove2me | Theorems.Thm_LaconicBarrier_we_laconic_argument
-- name    : LaconicBarrier.we_laconic_argument
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:34.693356+00:00
-- url     : https://prove2.me/theorems/b7befc04-493d-4776-a228-310114a2f276
-- title:
--   §7.1 — witness encryption gives a one-bit two-message laconic argument
-- statement:
--   Let $(\mathrm{Enc}, \mathrm{Dec})$ be a witness encryption scheme for an NP relation $\mathcal R$, for one-bit messages, correct up to a negligible error. In the argument where the verifier sends $ct \leftarrow \mathrm{Enc}(1^\lambda, x, \mu)$ for a uniform bit $\mu$ and the prover returns $\pi = \mathrm{Dec}(ct, w)$:
--
--   1. the verifier and the prover run in polynomial time;
--   2. the completeness error is at most the decryption error: if $\Pr[\mathrm{Dec}(\mathrm{Enc}(1^\lambda, x, \mu), w) = \mu] \ge 1 - \kappa$ for both bits $\mu$, the honest prover is accepted with probability at least $1-\kappa$;
--   3. the prover sends exactly one bit;
--   4. the soundness game, with baseline $c_0 = 1/2$, is exactly the fixed-message witness-encryption game, so a reduction for one is a reduction for the other with the same query count.
--
--   Witness encryption thereby enters the general machinery of §6 with $\ell_P = 1$, so the $2^{\ell_P}$ factor of the complementation step is a constant.
--
--   Differences from the source:
--   - reading: witness encryption for R with message length ℓ(λ) (Definition 4.8) → one-bit messages; Dec outputs [µ] or any other string (⊥); security is the fixed-message game with the pair (0, 1); reason: §7.1 uses WE 'supporting one-bit messages', and the query count refers to the ciphertext-to-bit oracle (p.18)
--   - encoding: the prover returns π = Dec(ct, w); 'the prover sends exactly one bit' → π = bitOf(Dec(ct, w)): [1] stays [1], every other output (including ⊥) becomes [0]; reason: makes the one-bit message literal; a failure symbol is a losing answer either way
--   - encoding: 'the soundness game is exactly the fixed-message witness-encryption game'; 'the reduction and its query complexity are preserved' → equality of the two families of two-message games (coins, challenges, winning predicate, baseline); reason: every reduction notion is a function of the family, so equality transfers reductions and query counts
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §7.1, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_LaconicBarrier_weArgument
import Definitions.Def_LaconicBarrier_WEScheme_source
import Definitions.Def_LaconicBarrier_LaconicArg_source

namespace LaconicBarrier

/-- **Witness encryption gives a one-bit two-message laconic argument** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), §7.1, p.45). Let
`(Enc, Dec)` be a witness encryption scheme for the relation `R`, for one-bit messages. In the
argument `weArgument` (the verifier sends `ct ← Enc(1^λ, x, µ)` for a uniform bit `µ`, the prover
returns `π = Dec(ct, w)`, the verifier accepts iff `π = µ`):

1. the verifier and the prover run in polynomial time;
2. the completeness error is at most the decryption error: if `Pr[Dec(Enc(1^λ, x, µ), w) = µ] ≥ 1 − κ`
   for both bits `µ`, the honest prover is accepted with probability `≥ 1 − κ`;
3. the prover sends exactly one bit;
4. the soundness game with baseline `c₀ = 1/2` is exactly the fixed-message witness-encryption game,
   so a reduction for one is a reduction for the other, with the same query count. -/
theorem we_laconic_argument (Rel : List Bool → List Bool → Prop) (E : WEScheme)
    (hE : E.IsWE Rel) :
    (weArgument E).IsPPT ∧
    (∀ (lam : ℕ) (x w : List Bool) (κ : ℝ), (∀ mu : Bool, 1 - κ ≤ E.decProb lam x mu w) →
      1 - κ ≤ (weArgument E).honestAcc lam x w) ∧
    (∀ (pk x w : List Bool) (ρ : Fin ((weArgument E).pcoins pk x w) → Bool),
      ((weArgument E).P pk x w ρ).length = 1) ∧
    (weArgument E).source (1 / 2) (by norm_num) (by norm_num) = E.source := by sorry

end LaconicBarrier
