-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_extraction
-- name    : GOSNIZK.BGNCommit.extraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:11.726151+00:00
-- url     : https://prove2.me/theorems/fb617280-26c6-4010-954d-898f762e40b5
-- title:
--   Figure 1 — extraction: $c^q = (g^q)^m$ and $\mathrm{Ext}$ recovers $m \bmod p$ on a binding key
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$ and let $h = g^{px}$, $x \in \mathbb Z_q^*$, be a perfectly binding key. For every message $m \in \mathbb Z_n$ and randomizer $r \in \mathbb Z_n$, the commitment $c = g^m h^r$ satisfies
--   $$c^q = (g^m h^r)^q = (g^q)^m,$$
--   and the extractor of Figure 1 (exhaustive search for the exponent of $c^q$ in base $g^q$) returns $\mathrm{Ext}_{xk}(c) = m \bmod p$.
--
--   This is the extraction step behind the perfect extractability of the scheme: knowing $q$ suffices to read the message (up to its residue modulo $p$) out of a commitment.
--
--   **Formalization Note** The extractor returns the least $k < p$ with $c^q = (g^q)^k$, read in $\mathbb Z_p$. The statement holds for every message, not only for $m \in \{0,1\}$; the perfect extractability conjunct of Theorem 2 is its restriction to $\{0,1\}$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 10, Figure 1 (Extraction); p. 9, proof of Theorem 2

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem extraction {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h) (m r : ZMod S.n) :
    S.com h m r ^ S.q = (S.g ^ S.q) ^ m.val ∧ S.Ext (S.com h m r) = S.toZp m := by sorry

end GOSNIZK.BGNCommit
