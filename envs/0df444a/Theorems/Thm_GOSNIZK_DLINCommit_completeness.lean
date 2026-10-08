-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_completeness
-- name    : GOSNIZK.DLINCommit.completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:59.216359+00:00
-- url     : https://prove2.me/theorems/11db1f09-3166-4f0f-893c-d3fe92ee3a98
-- title:
--   Proof of Theorem 4 (p. 13) — perfect completeness of the 0/1 proof (corrected Figure 2) on either key
-- statement:
--   Let $(p, \mathbb G, \mathbb G_T, e, g)$ be a DLIN bilinear group and let $ck$ be a commitment key in the support of the perfectly binding or the perfectly hiding generator of Figure 2. For every $m \in \{0, 1\}$, every randomizer $(r, s) \in \mathbb Z_p^2$ and every proof randomness $t \in \mathbb Z_p$,
--   $$V_{01}\bigl(ck,\ \mathrm{com}(m; r, s),\ P_{01}(ck, m, (r, s); t)\bigr) \text{ accepts.}$$
--
--   This is the perfect completeness property of §3 for the scheme of Figure 2.
--
--   **Formalization Note** $P_{01}$ is the prover of Figure 2 with the signs of $t$ in $\pi_{12}$ and $\pi_{21}$ swapped. With the signs as printed the statement is false whenever $2t \ne 0$ in $\mathbb Z_p$: the fourth and sixth verification equations fail by the factors $e(g,g)^{2xt}$ and $e(g,g)^{-2yt}$, where $f = g^x$, $h = g^y$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 13, proof of Theorem 4 ('Perfect completeness ... follows from direct verification'); Figure 2, p. 12

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

namespace GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- Proof of Theorem 4, p. 13: perfect completeness of the 0/1 proof of Figure 2 (with the corrected signs
of `t` in `π₁₂`, `π₂₁`; see `P01`) on either type of key. -/
theorem completeness (S : DLINSetup G GT) : S.PerfectCompleteness := by sorry

end GOSNIZK.DLINCommit
