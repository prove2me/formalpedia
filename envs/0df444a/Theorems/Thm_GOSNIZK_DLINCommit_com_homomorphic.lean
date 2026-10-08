-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_com_homomorphic
-- name    : GOSNIZK.DLINCommit.com_homomorphic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:47.389769+00:00
-- url     : https://prove2.me/theorems/55784346-ebf4-4bf2-bdb0-7cc4dfd089ff
-- title:
--   Proof of Theorem 4 (p. 11) — the DLIN commitment is homomorphic on either type of key
-- statement:
--   Let $(p, \mathbb G, \mathbb G_T, e, g)$ be a DLIN bilinear group and let $ck = (f, h, u, v, w)$ be a commitment key in the support of the perfectly binding or of the perfectly hiding key generator of Figure 2. Then for all messages $m_1, m_2 \in \mathbb Z_p$ and randomizers $(r_1, s_1), (r_2, s_2) \in \mathbb Z_p^2$,
--   $$\mathrm{com}(m_1 + m_2; r_1 + r_2, s_1 + s_2) = \mathrm{com}(m_1; r_1, s_1)\,\mathrm{com}(m_2; r_2, s_2),$$
--   where the product on the right is entry-wise multiplication in $\mathbb G^3$.
--
--   This is the homomorphic property of a homomorphic proof commitment (§3); the Circuit-SAT proof of Section 6 uses it to combine commitments to wires.
--
--   **Formalization Note** Exponents in $\mathbb Z_p$ act through representatives in $\{0, \dots, p-1\}$; the statement is the `Homomorphic` property of the mission's definitions.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 11, proof of Theorem 4 (homomorphism display)

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

namespace GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- Proof of Theorem 4, p. 11: the commitment of Figure 2 is homomorphic under entry-wise multiplication on
either type of commitment key. -/
theorem com_homomorphic (S : DLINSetup G GT) : S.Homomorphic := by sorry

end GOSNIZK.DLINCommit
