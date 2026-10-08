-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_binding_key_decomposition
-- name    : GOSNIZK.BGNCommit.binding_key_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:43.537207+00:00
-- url     : https://prove2.me/theorems/b2ce544d-9ccb-402d-b8c7-bf29f9360a5e
-- title:
--   Proof of Theorem 2 — on a binding key every $c$ is $g^m h^r$ with $m \in \mathbb Z_p$ uniquely defined
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$ and let $h = g^{px}$, $x \in \mathbb Z_q^*$, be a perfectly binding key. Every $c \in \mathbb G$ can be written
--   $$c = g^m h^r \qquad (m, r \in \mathbb Z_n),$$
--   and the residue $m \bmod p$ is the same for every such representation.
--
--   This is the first step of the soundness argument: an arbitrary group element the adversary presents is a commitment to a well-defined message of $\mathbb Z_p$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 9, proof of Theorem 2 (perfect soundness)

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem binding_key_decomposition {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT]
    [Fintype GT] (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h) (c : G) :
    ∃ m r : ZMod S.n, c = S.com h m r ∧
      ∀ m' r' : ZMod S.n, c = S.com h m' r' → S.toZp m' = S.toZp m := by sorry

end GOSNIZK.BGNCommit
