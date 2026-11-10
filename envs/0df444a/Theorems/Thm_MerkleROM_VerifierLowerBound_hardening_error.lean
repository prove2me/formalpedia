-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_hardening_error
-- name    : MerkleROM.VerifierLowerBound.hardening_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:42.437747+00:00
-- url     : https://prove2.me/theorems/86362f89-c59f-4fc5-a03f-0f249e97a8a1
-- title:
--   Lemma 5.2 — Hardening error
-- statement:
--   Consider an efficient commitment family and a polynomially bounded length family $n=\Omega(\lambda)$ in the source oracle regime. Suppose that, eventually, Alice sends at most $n$ bits on every supported execution of Algorithm 2. Then
--
--   $$\Pr[\mathrm{hardening\ error}]=\operatorname{negl}(\lambda).$$
--
--   This is the actual event that a hardening invocation in the protocol returns fail. The message-cap hypothesis concerns the full communication experiment; no independence or uniformity after conditioning on Alice's adaptively produced transcript is assumed.
--
--   The statement provides the hardening error estimate used under the main theorem's compression contradiction.
--
--   Differences from the source:
--   - encoding: asymptotic cryptographic parameter regime → existential threshold before all sufficiently large security parameters; no polynomial degree fixed; reason: finite initial changes preserve security, and n=Omega(lambda) supplies positive growing vector length
--   - encoding: Algorithm 2 after Fact 1 → the actual protocol law for normalizeFamily F, with Q increased by kn; reason: normalization queries are charged before setting p; all errors use one shared oracle and actual messages
--   - generalization: the secure vector-commitment setting of Section 5 → only the explicitly stated efficiency or security properties needed by this local result; reason: the fixed-input hardening estimate and message cap do not require completeness or binding; every secure source instance satisfies these hypotheses
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 17, Lemma 5.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem hardening_error (F : SchemeFamily) (n : ℕ → ℕ)
    (hF : Efficient F) (htheta : OracleLengths F.theta)
    (hn : PolynomiallyBounded n) (hnl : OmegaSecurity n)
    (hcap : MessageCap F n) :
    Negligible (errorProbability F n .hardeningError) := by sorry

end MerkleROM.VerifierLowerBound
