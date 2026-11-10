-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_binding_error
-- name    : MerkleROM.VerifierLowerBound.binding_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:53.098536+00:00
-- url     : https://prove2.me/theorems/b3ccc4dc-9882-43f1-91fa-3b4de84463f8
-- title:
--   Lemma 5.4 — Binding error
-- statement:
--   Let $\Sigma$ be an efficient position-binding vector-commitment family, and let $n(\lambda)$ be any polynomially bounded vector length. In the communication protocol,
--
--   $$\Pr[\mathrm{binding\ error}]=\operatorname{negl}(\lambda).$$
--
--   The event includes double certification during hardening, wrong-bit certification checked by Alice, and double certification at Bob's termination check. Each opening is evaluated with the same sampled oracle. Query complexity, rather than computation time, controls the joint Alice–Bob simulation.
--
--   This connects all of the protocol's binding failures to Definition 2 for adversarial commitments.
--
--   Differences from the source:
--   - encoding: Algorithm 2 after Fact 1 → the actual protocol law for normalizeFamily F, with Q increased by kn; reason: normalization queries are charged before setting p; all errors use one shared oracle and actual messages
--   - generalization: the secure vector-commitment setting of Section 5 → only the explicitly stated efficiency or security properties needed by this local result; reason: each binding-error branch supplies two accepted openings; global completeness is unnecessary; every secure source instance satisfies these hypotheses
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 20, Lemma 5.4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem binding_error (F : SchemeFamily) (n : ℕ → ℕ)
    (hF : Efficient F) (hbind : PositionBinding F)
    (hn : PolynomiallyBounded n) :
    Negligible (errorProbability F n .bindingError) := by sorry

end MerkleROM.VerifierLowerBound
