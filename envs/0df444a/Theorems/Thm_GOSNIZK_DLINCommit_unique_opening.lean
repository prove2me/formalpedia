-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_unique_opening
-- name    : GOSNIZK.DLINCommit.unique_opening
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:56.221676+00:00
-- url     : https://prove2.me/theorems/411d4cc7-f213-4a3d-ab40-77f97f94605f
-- title:
--   Proof of Theorem 4 (p. 13) — on a binding key every c ∈ 𝔾³ has exactly one opening (m, r, s)
-- statement:
--   Let $(p, \mathbb G, \mathbb G_T, e, g)$ be a DLIN bilinear group and let $ck = (f, h, u, v, w)$ be a perfectly binding commitment key of Figure 2. Then the map
--   $$\mathbb Z_p^3 \to \mathbb G^3, \qquad (m, r, s) \mapsto \mathrm{com}(m; r, s) = (u^m f^r, v^m h^s, w^m g^{r+s})$$
--   is a bijection: every $c \in \mathbb G^3$ uniquely defines $m, r, s \in \mathbb Z_p$ with $c = \mathrm{com}(m; r, s)$.
--
--   In particular the commitment is perfectly binding; the soundness argument of Theorem 4 starts from this decomposition.
--
--   **Formalization Note** The paper writes "$c_2 = v^m h^r$", a typo for $v^m h^s$; the statement uses $h^s$, as in the definition of the commitment.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 13, proof of Theorem 4 (with p. 12: 'perfectly binding ... when (u, v, w) is not a linear tuple')

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

namespace GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- Proof of Theorem 4, p. 13: on a perfectly binding key every `c ∈ 𝔾³` uniquely defines
`m, r, s ∈ ℤ_p` with `c = (u^m f^r, v^m h^s, w^m g^{r+s})`, i.e. `(m, r, s) ↦ com(m; r, s)` is a
bijection `ℤ_p³ → 𝔾³`. -/
theorem unique_opening (S : DLINSetup G GT) (ck : CommitKey G) (xk : ZMod S.p × ZMod S.p × ZMod S.p)
    (hck : S.IsBindingKey ck xk) :
    Function.Bijective
      (fun mrs : ZMod S.p × ZMod S.p × ZMod S.p => S.com ck mrs.1 mrs.2.1 mrs.2.2) := by sorry

end GOSNIZK.DLINCommit
