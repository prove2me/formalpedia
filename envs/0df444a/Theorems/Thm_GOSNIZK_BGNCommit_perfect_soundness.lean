-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_perfect_soundness
-- name    : GOSNIZK.BGNCommit.perfect_soundness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:34.682853+00:00
-- url     : https://prove2.me/theorems/9cc9c3a5-fa45-455a-bb2c-4e6fd9d0d3ee
-- title:
--   Proof of Theorem 2 — perfect soundness of the 0/1 proof on binding keys
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$ and let $h = g^{px}$, $x \in \mathbb Z_q^*$, be a perfectly binding key. If $c, \pi \in \mathbb G$ pass verification,
--   $$e(c, c g^{-1}) = e(h, \pi),$$
--   then $c$ is a commitment to $0$ or to $1$: there are $m \in \{0, 1\}$ and $r \in \mathbb Z_n$ with $c = g^m h^r$.
--
--   This is the perfect soundness of the non-interactive proof that a commitment contains $0$ or $1$; it holds for every pair $(c, \pi)$, so against every adversary, however powerful.
--
--   **Formalization Note** The paper's probability-one statement over $(ck, xk) \leftarrow K_{\mathrm{binding}}$ and an adversary's output $(c, \pi)$ is stated for every key in the support of $K_{\mathrm{binding}}$ and every $(c, \pi)$; for unbounded adversaries the two are equivalent.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 9, proof of Theorem 2 (perfect soundness); p. 7, Perfect soundness

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem perfect_soundness {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h) (c π : G) (hv : S.V01 h c π) :
    ∃ m r : ZMod S.n, (m = 0 ∨ m = 1) ∧ c = S.com h m r := by sorry

end GOSNIZK.BGNCommit
