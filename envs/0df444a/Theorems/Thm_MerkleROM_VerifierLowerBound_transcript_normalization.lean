-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_transcript_normalization
-- name    : MerkleROM.VerifierLowerBound.transcript_normalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:57.40943+00:00
-- url     : https://prove2.me/theorems/b38fd0e4-8fee-4d55-8dd8-42d86ddd1c99
-- title:
--   Fact 1 — Normalize deterministic verifiers
-- statement:
--   Let $\Sigma$ be any vector-commitment family with deterministic adaptive verifiers and polynomial query bounds $Q$ and $k$. The explicitly constructed normalized family preserves completeness and position binding, retains the exact commitment distribution under every fixed oracle, and satisfies
--
--   $$Q'\le Q+kn,\qquad k'\le k,\qquad |\pi_i'|=(\theta+\lambda)k.$$
--
--   Every normalized verifier's query list is independent of oracle answers. Each normalized honest witness is the encoded list of query-answer pairs produced by original verification, padded by actual dummy calls when necessary. The verifier also checks existence of an original accepting witness under those entries.
--
--   This transformation justifies using transcript witnesses in the lower-bound protocol while retaining the full scope of arbitrary original deterministic verifiers.
--
--   Differences from the source:
--   - encoding: one-based bit strings and oracle algorithms → Fin-indexed bit strings and PMFs on adaptive probe trees; reason: the same finite coordinates and independent private randomness; every call counts and local computation has no bound
--   - encoding: at most k original queries; displayed k-pair witnesses → exactly k pairs by padding with actual dummy queries; reason: padding costs at most the unused part of the k-call allowance and changes no acceptance decision
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 15, Fact 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem transcript_normalization (F : SchemeFamily) (hF : Efficient F) :
    Efficient (normalizeFamily F) ∧
    (Complete F → Complete (normalizeFamily F)) ∧
    (PositionBinding F → PositionBinding (normalizeFamily F)) ∧
    ∀ l n,
      let S := F.scheme l n
      let k := F.verifyQueries l n
      let S' := normalizeScheme S k
      QueryBounds S' (F.commitQueries l n + k*n) k ∧
      (∀ x (R : Bits (F.theta l) → Bits l),
        ((S'.commit x).map (fun a => (a.run R).commitment)) =
        ((S.commit x).map (fun a => (a.run R).commitment))) ∧
      (∀ x a, a ∈ (S'.commit x).support → ∀ R i,
        ((a.run R).witnesses i).length = (F.theta l+l)*k) ∧
      (∀ c i b w (R R' : Bits (F.theta l) → Bits l),
        ((S'.verify c i b w).transcript R).map Prod.fst =
        ((S'.verify c i b w).transcript R').map Prod.fst) := by sorry

end MerkleROM.VerifierLowerBound
