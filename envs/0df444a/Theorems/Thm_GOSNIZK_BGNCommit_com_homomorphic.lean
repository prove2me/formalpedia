-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_com_homomorphic
-- name    : GOSNIZK.BGNCommit.com_homomorphic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:53.316905+00:00
-- url     : https://prove2.me/theorems/a737784d-ca1b-403d-9b71-7cabfc2bcf0d
-- title:
--   Proof of Theorem 2 — the BGN commitment is homomorphic on either type of key
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$, and let $h$ be a perfectly binding key ($h = g^{px}$, $x \in \mathbb Z_q^*$) or a perfectly hiding key ($h = g^x$, $x \in \mathbb Z_n^*$). Then for all messages $m_1, m_2 \in \mathbb Z_n$ and randomizers $r_1, r_2 \in \mathbb Z_n$,
--   $$\mathrm{com}(m_1 + m_2; r_1 + r_2) = \mathrm{com}(m_1; r_1)\,\mathrm{com}(m_2; r_2).$$
--
--   This is the homomorphic property of a homomorphic proof commitment, the property that lets the Circuit-SAT proofs of the paper combine commitments to wire values.
--
--   **Formalization Note** Messages are taken in $\mathbb Z_n$ (see the definition of the scheme).
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 9, proof of Theorem 2

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem com_homomorphic {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h ∨ ∃ x, S.IsHidingKey h x)
    (m₁ r₁ m₂ r₂ : ZMod S.n) :
    S.com h (m₁ + m₂) (r₁ + r₂) = S.com h m₁ r₁ * S.com h m₂ r₂ := by sorry

end GOSNIZK.BGNCommit
