-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_trapdoor_opening
-- name    : GOSNIZK.DLINCommit.trapdoor_opening
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:48.028497+00:00
-- url     : https://prove2.me/theorems/2b0149ec-8833-4958-b7f7-2f341d6d3353
-- title:
--   Figure 2 (p. 12) — trapdoor opening: com(m; r, s) = com(m′; r − (m′ − m)r_u, s − (m′ − m)s_v) on a hiding key
-- statement:
--   Let $(p, \mathbb G, \mathbb G_T, e, g)$ be a DLIN bilinear group and let $ck = (f, h, u, v, w)$ be a perfectly hiding commitment key with trapdoor $tk = (r_u, s_v)$, i.e. $f = g^x$, $h = g^y$ with $x, y \ne 0$ and $(u, v, w) = (f^{r_u}, h^{s_v}, g^{r_u + s_v})$. Then for all $m, m', r, s \in \mathbb Z_p$,
--   $$\mathrm{com}(m; r, s) = \mathrm{com}\bigl(m';\ r - (m'-m) r_u,\ s - (m'-m) s_v\bigr).$$
--
--   So whoever holds the trapdoor can open a commitment made under a hiding key to any message; this is the trapdoor opening $\mathrm{Topen}$ of Figure 2.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 12, Figure 2 (Trapdoor opening)

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

namespace GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- Figure 2, p. 12 (trapdoor opening): on a perfectly hiding key with trapdoor `tk = (r_u, s_v)`,
`com(m; r, s) = com(m′; r − (m′ − m) r_u, s − (m′ − m) s_v)` for all `m, m′, r, s ∈ ℤ_p`. -/
theorem trapdoor_opening (S : DLINSetup G GT) (ck : CommitKey G) (ru sv : ZMod S.p)
    (hck : S.IsHidingKey ck (ru, sv)) (m r s m' : ZMod S.p) :
    S.com ck m r s = S.com ck m' (r - (m' - m) * ru) (s - (m' - m) * sv) := by sorry

end GOSNIZK.DLINCommit
