-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_soundness_order_step
-- name    : GOSNIZK.BGNCommit.soundness_order_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:30.648885+00:00
-- url     : https://prove2.me/theorems/84b5bd5c-befd-4b42-a96c-f94020dbc111
-- title:
--   Proof of Theorem 2 — if $e(g,g)^{m(m-1)}$ has order 1 or $q$ then $m \equiv 0$ or $1 \pmod p$
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$ and let $m \in \mathbb Z_n$. If $e(g,g)^{m(m-1)}$ has order $1$ or $q$, that is,
--   $$\big(e(g, g)^{m(m-1)}\big)^q = 1,$$
--   then $m \equiv 0 \pmod p$ or $m \equiv 1 \pmod p$.
--
--   This is the step of the soundness proof where the hypothesis that $e(g,g)$ generates $\mathbb G_T$ is used: a degenerate pairing would make the conclusion fail.
--
--   **Formalization Note** "Has order 1 or $q$" is stated as "its $q$-th power is $1$", which is equivalent since $q$ is prime. The exponent $m(m-1)$ is computed in $\mathbb Z_n$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 9, proof of Theorem 2 (perfect soundness)

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem soundness_order_step {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT]
    [Fintype GT] (S : BGNSetup G GT) (m : ZMod S.n)
    (hord : (S.e S.g S.g ^ (m * (m - 1)).val) ^ S.q = 1) :
    S.toZp m = 0 ∨ S.toZp m = 1 := by sorry

end GOSNIZK.BGNCommit
