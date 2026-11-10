-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_disjointness_error
-- name    : MerkleROM.VerifierLowerBound.disjointness_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:41.749994+00:00
-- url     : https://prove2.me/theorems/273cf4bd-56d5-4d4c-896a-0d2da4f20fcc
-- title:
--   Lemma 5.3 — Disjointness error
-- statement:
--   Consider an efficient commitment family in the source oracle regime and a polynomially bounded length family $n=\Omega(\lambda)$. If eventually $k\le\log_2 n$, then the actual communication protocol satisfies
--
--   $$\Pr[\mathrm{disjointness\ error}]=\operatorname{negl}(\lambda).$$
--
--   Disjointness error means that Alice's greedy residual-set selection reaches the threshold $\ell+\lambda$ in a reached round, where $\ell$ is the number of bits already sent. Correlations between the commitment, residual witnesses and oracle are included in the experiment.
--
--   The condition on $k$ belongs to this supporting lemma; the main theorem does not assume it.
--
--   Differences from the source:
--   - encoding: asymptotic cryptographic parameter regime → existential threshold before all sufficiently large security parameters; no polynomial degree fixed; reason: finite initial changes preserve security, and n=Omega(lambda) supplies positive growing vector length
--   - encoding: Algorithm 2 after Fact 1 → the actual protocol law for normalizeFamily F, with Q increased by kn; reason: normalization queries are charged before setting p; all errors use one shared oracle and actual messages
--   - generalization: the secure vector-commitment setting of Section 5 → only the explicitly stated efficiency or security properties needed by this local result; reason: initialization checks the honest witnesses on each reached run; the disjointness estimate needs neither a global completeness bound nor binding; every secure source instance satisfies these hypotheses
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 19, Lemma 5.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem disjointness_error (F : SchemeFamily) (n : ℕ → ℕ)
    (hF : Efficient F) (htheta : OracleLengths F.theta)
    (hn : PolynomiallyBounded n) (hnl : OmegaSecurity n)
    (hk : ∃ N, ∀ l ≥ N, (F.verifyQueries l (n l) : ℝ) ≤ Real.logb 2 (n l)) :
    Negligible (errorProbability F n .disjointnessError) := by sorry

end MerkleROM.VerifierLowerBound
