-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_trapdoor_opening
-- name    : GOSNIZK.BGNCommit.trapdoor_opening
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:18.050703+00:00
-- url     : https://prove2.me/theorems/71a22d6d-8ebb-448a-8a43-04649b5c448f
-- title:
--   Figure 1 — trapdoor opening: $g^m h^r = g^{m'} h^{r-(m'-m)/x}$ on a hiding key
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$ and let $h = g^x$ with $x \in \mathbb Z_n^*$ be a perfectly hiding key with trapdoor $x$. For all $m, r, m' \in \mathbb Z_n$,
--   $$g^{m'} h^{\,r - (m'-m)/x} = g^m h^r,$$
--   that is, $\mathrm{com}(m'; \mathrm{Topen}_{tk}(m, r, m')) = \mathrm{com}(m; r)$.
--
--   This is the perfect trapdoor opening property: with the trapdoor, a commitment made under a hiding key can be opened to any message.
--
--   **Formalization Note** $(m'-m)/x$ is $(m'-m)\,x^{-1}$ in $\mathbb Z_n$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 10, Figure 1 (Trapdoor opening)

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem trapdoor_opening {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (x : ZMod S.n) (hkey : S.IsHidingKey h x) (m r m' : ZMod S.n) :
    S.com h m' (S.Topen x m r m') = S.com h m r := by sorry

end GOSNIZK.BGNCommit
