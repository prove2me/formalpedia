-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_verifier_query_lower_bound
-- name    : MerkleROM.VerifierLowerBound.verifier_query_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:34:10.844413+00:00
-- url     : https://prove2.me/theorems/57416e6c-dfd0-489a-8f68-a1dc2bad95af
-- title:
--   Theorem 1 — Verifier query lower bound for vector commitments
-- statement:
--   Let $\Sigma=(\mathsf{Commit},\mathsf{Verify})$ be any complete, position-binding vector-commitment family in the random oracle model with deterministic, possibly adaptive verifiers and polynomial committer and verifier query complexity. The oracle is $R:\{0,1\}^{\theta(\lambda)}\to\{0,1\}^{\lambda}$, with polynomially related input and output lengths. Let $n(\lambda)$ be any polynomially bounded vector-length family with $n=\Omega(\lambda)$. Write $m(\lambda,n)$ for its fixed commitment bit length and $k(\lambda,n)$ for its worst-case verifier query bound. Then
--
--   $$\exists\lambda_0\ \forall\lambda\ge\lambda_0,\qquad 2+\bigl(3k(\lambda,n(\lambda))\theta(\lambda)\bigr)^{k(\lambda,n(\lambda))}\bigl(m(\lambda,n(\lambda))+\lambda\bigr)\ge n(\lambda).$$
--
--   Security is against every computationally unbounded polynomial-query adversary, including adversarial commitments, with two openings evaluated under a single sampled oracle. Completeness uses one negligible bound common to all honest vectors. Neither perfect completeness, a polynomial bound on commitment length, a fixed polynomial degree, $\theta=2\lambda$, nor $k\le\log n$ is an assumption.
--
--   This is the exact numerical lower bound of Theorem 1 and the sole mission goal.
--
--   Differences from the source:
--   - encoding: one-based bit strings and oracle algorithms → Fin-indexed bit strings and PMFs on adaptive probe trees; reason: the same finite coordinates and independent private randomness; every call counts and local computation has no bound
--   - encoding: asymptotic cryptographic parameter regime → existential threshold before all sufficiently large security parameters; no polynomial degree fixed; reason: finite initial changes preserve security, and n=Omega(lambda) supplies positive growing vector length
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 21, Theorem 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem verifier_query_lower_bound (F : SchemeFamily)
    (htheta : OracleLengths F.theta) (hF : Secure F) (n : ℕ → ℕ)
    (hn : PolynomiallyBounded n) (hnl : OmegaSecurity n) :
    ∃ N, ∀ l ≥ N,
      n l ≤ 2 + (3*F.verifyQueries l (n l)*F.theta l)^(F.verifyQueries l (n l)) *
        (F.size l (n l)+l) := by sorry

end MerkleROM.VerifierLowerBound
