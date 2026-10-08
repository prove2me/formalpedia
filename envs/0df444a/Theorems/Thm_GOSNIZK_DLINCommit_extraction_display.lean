-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_extraction_display
-- name    : GOSNIZK.DLINCommit.extraction_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:55.738575+00:00
-- url     : https://prove2.me/theorems/b734fe66-4cc5-4996-9fdc-d255cf33fe12
-- title:
--   Figure 2 (p. 12) — extraction: c₃ c₁^{−1/x} c₂^{−1/y} = (g^z)^m on a binding key
-- statement:
--   Let $(p, \mathbb G, \mathbb G_T, e, g)$ be a DLIN bilinear group and let $(ck, xk)$ be a perfectly binding key pair of Figure 2 with extraction key $xk = (x, y, z)$, $x, y, z \ne 0$. Then every commitment $c = (c_1, c_2, c_3) = \mathrm{com}(m; r, s)$ satisfies
--   $$c_3\, c_1^{-1/x}\, c_2^{-1/y} = (g^z)^m,$$
--   where $-1/x$ and $-1/y$ are computed in $\mathbb Z_p$.
--
--   Since $g^z$ generates $\mathbb G$, the left side determines $m$, and the extractor recovers a short message by exhaustive search.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 12, Figure 2 (Extraction)

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

namespace GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- Figure 2, p. 12 (extraction): on a perfectly binding key with extraction key `xk = (x, y, z)`, every
commitment `c = (c₁, c₂, c₃) = com(m; r, s)` satisfies `c₃ c₁^{−1/x} c₂^{−1/y} = (g^z)^m`. -/
theorem extraction_display (S : DLINSetup G GT) (ck : CommitKey G) (x y z : ZMod S.p)
    (hck : S.IsBindingKey ck (x, y, z)) (m r s : ZMod S.p) :
    (S.com ck m r s).2.2 * (S.com ck m r s).1 ^ (-1 / x).val * (S.com ck m r s).2.1 ^ (-1 / y).val =
      (S.g ^ z.val) ^ m.val := by sorry

end GOSNIZK.DLINCommit
