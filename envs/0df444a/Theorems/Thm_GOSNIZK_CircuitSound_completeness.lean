-- Prove2me | Theorems.Thm_GOSNIZK_CircuitSound_completeness
-- name    : GOSNIZK.CircuitSound.completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:56.655753+00:00
-- url     : https://prove2.me/theorems/5d046dd5-b53d-4787-b657-94913f7bcc5b
-- title:
--   Proof of Theorem 6 — the protocol of Figure 3 has perfect completeness
-- statement:
--   Let a homomorphic proof commitment scheme satisfy the homomorphic property and perfect completeness of the 0/1 proof. Then the Circuit SAT proof of Figure 3 has perfect completeness on keys of either mode: for every key $ck$ output by $K_{\mathrm{binding}}$ or $K_{\mathrm{hiding}}$, every NAND circuit $C$, every $w$ with $C(w)=1$ and every choice of the prover's randomness,
--   $$V\big(ck,\ C,\ P(ck,C,w)\big)=1.$$
--
--   Completeness on hiding keys is the completeness clause of Theorem 11 (p. 16), which refers back to the proof of Theorem 6.
--
--   **Formalization Note** No order bound on $\mathcal M$ is needed: for a satisfied gate the gate message $w_i+w_j+2w_k-2$ equals $w_i\oplus w_j\in\{0,1\}$ in every $\mathbb Z/N\mathbb Z$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, pp. 14–15, proof of Theorem 6 (first paragraph); p. 16, Theorem 11

import Mathlib
import Definitions.Def_GOSNIZK_CircuitSound_Protocol

namespace GOSNIZK.CircuitSound

/-- Perfect completeness of the protocol of Figure 3 (Groth, Ostrovsky, Sahai, *New Techniques for
Noninteractive Zero-Knowledge*, J. ACM 59(3) (2012), authors' version of March 7, 2011, proof of
Theorem 6, pp. 14–15): it follows from the homomorphic property and the perfect completeness of the
0/1 proofs, and holds on keys of either mode. -/
theorem completeness {N : ℕ} {R C CK XK TK Rp Prf : Type} [AddCommGroup R] [Fintype R] [CommGroup C] [Fintype C]
    [Fintype Rp] [Nonempty Rp] (S : Scheme N R C CK XK TK Rp Prf)
    (hhom : S.Homomorphic) (hcomp01 : S.PerfectCompleteness01) :
    S.CircuitPerfectCompleteness := by sorry

end GOSNIZK.CircuitSound
