-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_completeness_display
-- name    : GOSNIZK.BGNCommit.completeness_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:31.043024+00:00
-- url     : https://prove2.me/theorems/9c95afb1-7f44-4c80-bb10-87cdf1e626e5
-- title:
--   Proof of Theorem 2 — $e(c, cg^{-1}) = e(g,g)^{m(m-1)} e(h^r, g^{2m-1}h^r) = e(h, \pi)$
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$, let $h$ be a perfectly binding key ($h = g^{px}$, $x \in \mathbb Z_q^*$) or a perfectly hiding key ($h = g^x$, $x \in \mathbb Z_n^*$), and let $c = g^m h^r$ with $m, r \in \mathbb Z_n$. Then
--   $$e(c, c g^{-1}) = e(g^m h^r, g^{m-1} h^r) = e(g, g)^{m(m-1)}\, e(h^r, g^{2m-1} h^r),$$
--   and, if moreover $m \in \{0, 1\}$, then
--   $$e(c, c g^{-1}) = e(h, \pi), \qquad \pi = P_{01}(ck, m, r) = (g^{2m-1} h^r)^r .$$
--
--   The first identity, valid for every $m$, is the computation that both completeness and soundness rest on; the second says the honest proof is accepted (perfect completeness).
--
--   **Formalization Note** Exponents are elements of $\mathbb Z_n$ ($m(m-1)$ and $2m-1$ are computed in $\mathbb Z_n$). As on the page ("no matter whether $ck$ is a perfect binding key or a perfect hiding key"), $h$ is assumed to be a key of either kind.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 9, proof of Theorem 2 (perfect completeness)

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem completeness_display {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT]
    [Fintype GT] (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h ∨ ∃ x, S.IsHidingKey h x)
    (m r : ZMod S.n) :
    S.e (S.com h m r) (S.com h m r * S.g⁻¹) =
        S.e S.g S.g ^ (m * (m - 1)).val * S.e (h ^ r.val) (S.g ^ (2 * m - 1).val * h ^ r.val) ∧
      ((m = 0 ∨ m = 1) → S.e (S.com h m r) (S.com h m r * S.g⁻¹) = S.e h (S.P01 h m r)) := by sorry

end GOSNIZK.BGNCommit
