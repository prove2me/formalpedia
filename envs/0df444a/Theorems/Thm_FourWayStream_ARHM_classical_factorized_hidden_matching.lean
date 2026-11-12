-- Prove2me | Theorems.Thm_FourWayStream_ARHM_classical_factorized_hidden_matching
-- name    : FourWayStream.ARHM.classical_factorized_hidden_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:29.093593+00:00
-- url     : https://prove2.me/theorems/a5737dfa-0121-4da6-af98-b58732789a4d
-- title:
--   Lemma 5.11 — classical factorized Hidden Matching: $p-\tfrac12\le(1+c)/\sqrt{N-1}$
-- statement:
--   **Lemma 5.11 (Classical factorized Hidden Matching).** Let $F$ be any one-factorization of $K_N$, and let $X\in\{0,1\}^N$ and $K\in[N-1]$ be independent and uniform. Alice receives $X$, Bob receives $K$ and must output an edge of $F_K$ with its parity. A public-coin classical one-way protocol of $c$ bits that succeeds with probability $p$ satisfies
--   $$p-\frac12\le\frac{1+c}{\sqrt{N-1}}.$$
--   In particular, $c\ge(p-\tfrac12)\sqrt{N-1}-1$, so success $p>1/2$ requires $c=\Omega_p(\sqrt N)$ bits.
--
--   This is the classical Hidden Matching lower bound with Bob's matching drawn from a fixed public one-factorization; it gives the classical random-order bound (Proposition 5.12).
--
--   **Formalization Note** "$c$ bits" means at most $2^c$ messages. The protocol is a single-request instance of the classical sequential protocols of the mission.
--
--   Differences from the source:
--   - generalization: a public-coin classical one-way protocol → Alice may also use private randomness and Bob may answer at random; reason: protocols with deterministic players given the coins are a special case
--   - encoding: "In particular, success p > 1/2 requires c = Ω_p(√N) bits" → (p − 1/2)·√(N − 1) − 1 ≤ c; reason: the explicit form of the consequence, a rearrangement of the main inequality
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.2, p.23, Lemma 5.11

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Lemma 5.11 (Classical factorized Hidden Matching), p.23. Let `F` be any one-factorization of
`K_N`, and let `X ∈ {0,1}^N` and `K ∈ [N − 1]` be independent and uniform. A public-coin classical
one-way protocol of `c` bits (Alice sends one of at most `2^c` messages; Bob, given `K`, answers with
an edge of `F_K` and a bit) that succeeds with probability `p` satisfies `p − 1/2 ≤ (1 + c)/√(N − 1)`;
in particular `c ≥ (p − 1/2)√(N − 1) − 1`. -/
theorem classical_factorized_hidden_matching (N : ℕ) (F : Fin (N - 1) → Finset (Sym2 (Fin N)))
    (hF : IsOneFactorization F) {nR : ℕ} (P : CSeqProtocol N 1 (Fin (N - 1)) nR) (hP : P.Valid)
    (c : ℕ) (hc : P.M ≤ 2 ^ c) :
    P.jointSucc F (uniformFactor N) - 1 / 2 ≤ (1 + c) / Real.sqrt ((N : ℝ) - 1) ∧
    (P.jointSucc F (uniformFactor N) - 1 / 2) * Real.sqrt ((N : ℝ) - 1) - 1 ≤ c := by sorry

end FourWayStream.ARHM
