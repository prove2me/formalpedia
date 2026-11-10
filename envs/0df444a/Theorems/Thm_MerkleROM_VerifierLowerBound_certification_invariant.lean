-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_certification_invariant
-- name    : MerkleROM.VerifierLowerBound.certification_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:50.428701+00:00
-- url     : https://prove2.me/theorems/1d78a2fe-35ac-4900-9eaa-1132b4a32720
-- title:
--   Fact 2 — Certification progress at reached rounds
-- statement:
--   Let $\Sigma$ have committer and deterministic verifier query bounds $Q,k$, and let oracle bit lengths $\theta,\lambda$ be positive. Fix a vector $x$, an independently selected honest committer tree and an oracle. For every reached completed round $i$ of Algorithm 2 and every index $j$,
--
--   $$j\text{ is certified after round }i\quad\lor\quad |\operatorname{queries}(\pi_j)\cap\operatorname{dom}(T_i)|\ge i.$$
--
--   Only rounds actually completed without an earlier error are recorded. A successful early termination creates no later rounds. The query set is the set of distinct actual inputs in honest verification, and $T_i$ is the computed round table.
--
--   This is the full two-clause progress invariant, including every index at every reached round.
--
--   Differences from the source:
--   - encoding: the protocol does not terminate before the round under consideration → membership in the computed list of completed round snapshots; reason: the source proof is local to reached rounds and does not require a fictitious continuation after success
--   - generalization: normalized witnesses list their oracle queries → honest query sets are obtained from actual deterministic verification transcripts; reason: for normalized verifiers these are exactly the source witness inputs; the invariant also applies before explicitly serializing those transcripts
--   - generalization: the secure vector-commitment setting of Section 5 → only the explicitly stated efficiency or security properties needed by this local result; reason: each reached run has passed its honest verification check; the round invariant does not use global completeness or binding; every secure source instance satisfies these hypotheses
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 21, Fact 2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem certification_invariant {theta lam n m : ℕ}
    (S : Scheme theta lam n m) (Q k : ℕ) (hS : QueryBounds S Q k)
    (htheta : 0 < theta) (hlam : 0 < lam) (x : Bits n)
    (a : Tree (Bits theta) (Bits lam) (HonestOutput n m))
    (ha : a ∈ (S.commit x).support) (R : Bits theta → Bits lam)
    (round : RoundSnapshot theta lam)
    (hround : round ∈ (protocolRun S Q k x a R).rounds) :
    ∀ j : Fin n, Certified S k (a.run R).commitment round.table j ∨
      round.round ≤ (tableDomain (honestTables S x (a.run R) R j) ∩ tableDomain round.table).card := by sorry

end MerkleROM.VerifierLowerBound
