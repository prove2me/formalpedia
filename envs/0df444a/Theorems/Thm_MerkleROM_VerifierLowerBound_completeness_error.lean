-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_completeness_error
-- name    : MerkleROM.VerifierLowerBound.completeness_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:29.122498+00:00
-- url     : https://prove2.me/theorems/ce89714d-f036-4fb6-9382-e9013523048b
-- title:
--   Lemma 5.5 — Completeness error
-- statement:
--   Let $\Sigma$ be an efficient vector-commitment family satisfying Definition 1, and let $n(\lambda)$ be any polynomially bounded length family. For the source's communication experiment,
--
--   $$\Pr[\mathrm{completeness\ error}]=\operatorname{negl}(\lambda).$$
--
--   The probability averages over the uniform honest vector, the single sampled oracle and independent committer randomness. Definition 1 uses a common negligible bound over all honest vectors, so the statement includes the event that any of the $n$ honest openings fails.
--
--   This controls initialization failure without requiring perfect completeness.
--
--   Differences from the source:
--   - encoding: Algorithm 2 after Fact 1 → the actual protocol law for normalizeFamily F, with Q increased by kn; reason: normalization queries are charged before setting p; all errors use one shared oracle and actual messages
--   - generalization: the secure vector-commitment setting of Section 5 → only the explicitly stated efficiency or security properties needed by this local result; reason: initialization failure uses completeness; no binding assumption is needed; every secure source instance satisfies these hypotheses
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 21, Lemma 5.5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem completeness_error (F : SchemeFamily) (n : ℕ → ℕ)
    (hEff : Efficient F) (hF : Complete F) (hn : PolynomiallyBounded n) :
    Negligible (errorProbability F n .completenessError) := by sorry

end MerkleROM.VerifierLowerBound
