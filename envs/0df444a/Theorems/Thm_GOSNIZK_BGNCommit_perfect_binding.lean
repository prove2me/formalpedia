-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_perfect_binding
-- name    : GOSNIZK.BGNCommit.perfect_binding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:09.624412+00:00
-- url     : https://prove2.me/theorems/c0c2e663-d475-418c-9d45-4d1a43779dc8
-- title:
--   Proof of Theorem 2 — perfect binding when $h$ has order $q$
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$ and let $h = g^{px}$ with $x \in \mathbb Z_q^*$ be a perfectly binding key. If two openings give the same commitment,
--   $$g^{m_1} h^{r_1} = g^{m_2} h^{r_2} \qquad (m_1, r_1, m_2, r_2 \in \mathbb Z_n),$$
--   then $m_1 \equiv m_2 \pmod p$.
--
--   Since the message space of the scheme is $\mathbb Z_p$, this says that a commitment under a binding key determines its message: no two openings carry different messages.
--
--   **Formalization Note** Messages are represented in $\mathbb Z_n$ and compared after reduction modulo $p$; this is the paper's statement for the message space $\mathbb Z_p$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 9, proof of Theorem 2; p. 7, Perfect binding

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem perfect_binding {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h)
    (m₁ r₁ m₂ r₂ : ZMod S.n) (hc : S.com h m₁ r₁ = S.com h m₂ r₂) :
    S.toZp m₁ = S.toZp m₂ := by sorry

end GOSNIZK.BGNCommit
