-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_communication_bound
-- name    : MerkleROM.VerifierLowerBound.communication_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:50.134224+00:00
-- url     : https://prove2.me/theorems/3c767550-a35e-4472-b331-309c17c2c414
-- title:
--   Fact 3 — Communication bound
-- statement:
--   Let $\Sigma$ have committer and deterministic verifier query bounds $Q,k$, fixed commitment length $m$, and positive oracle input and output bit lengths $\theta,\lambda$. On every supported honest commitment execution and every oracle, the actual total number of bits Alice sends in Algorithm 2 satisfies
--
--   $$\ell_{\mathrm{total}}\le(3k\theta)^k(m+\lambda).$$
--
--   The counted messages include the commitment and every padded query message sent before termination, including error termination. No expected-length interpretation is used. The $k=0$ case is included with the ordinary convention $0^0=1$.
--
--   This supplies the exact source constant for the lower bound; the protocol padding is $2k\theta(\ell+\lambda)$ bits.
--
--   Differences from the source:
--   - encoding: query sets padded to the prescribed bit length → delimiter-coded query lists padded with zero bits; reason: one delimiter per theta-bit input plus an end marker fits the source factor 2 whenever a message is sent; Bob decodes the actual bits
--   - generalization: normalized witnesses list their oracle queries → honest query sets are obtained from actual deterministic verification transcripts; reason: normalization has the same query sets; the bound additionally holds for the transcript implementation of an adaptive original verifier
--   - generalization: the secure vector-commitment setting of Section 5 → only the explicitly stated efficiency or security properties needed by this local result; reason: the message length bound is pathwise and does not use completeness or binding; every secure source instance satisfies these hypotheses
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 22, Fact 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem communication_bound {theta lam n m : ℕ}
    (S : Scheme theta lam n m) (Q k : ℕ) (hS : QueryBounds S Q k)
    (htheta : 0 < theta) (hlam : 0 < lam) (x : Bits n)
    (a : Tree (Bits theta) (Bits lam) (HonestOutput n m))
    (ha : a ∈ (S.commit x).support) (R : Bits theta → Bits lam) :
    bitsSent (protocolRun S Q k x a R) ≤ (3*k*theta)^k*(m+lam) := by sorry

end MerkleROM.VerifierLowerBound
