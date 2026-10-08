-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_soundness_step
-- name    : GOSNIZK.DLINCommit.soundness_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:03.525981+00:00
-- url     : https://prove2.me/theorems/c16eb166-d938-4867-8abb-b0fb7e283858
-- title:
--   Proof of Theorem 4 (p. 13) — on a binding key an accepted c or c · com(−1; 0, 0) is a commitment to 0
-- statement:
--   Let $(p, \mathbb G, \mathbb G_T, e, g)$ be a DLIN bilinear group and $ck = (f, h, u, v, w)$ a perfectly binding commitment key of Figure 2. If $V_{01}(ck, c, \pi)$ accepts for $c = (c_1, c_2, c_3) \in \mathbb G^3$ and $\pi \in \mathbb G^6$, then
--
--   1. at least one of $(c_1, c_2, c_3)$ and $(c_1u^{-1}, c_2v^{-1}, c_3w^{-1})$ is a linear tuple with respect to $(f, h, g)$, and
--   2. $c$ or $c \cdot \mathrm{com}(-1; 0, 0)$ is a commitment to $0$:
--   $$\exists\, r, s \in \mathbb Z_p:\ c = \mathrm{com}(0; r, s) \qquad \text{or} \qquad \exists\, r, s \in \mathbb Z_p:\ c \cdot \mathrm{com}(-1; 0, 0) = \mathrm{com}(0; r, s).$$
--
--   By the homomorphic property the second alternative says that $c$ is a commitment to $1$, which is perfect soundness.
--
--   **Formalization Note** The paper writes "$cw^{-1}$" for the third entry, a typo for $c_3 w^{-1}$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 13, proof of Theorem 4 ('so at least one of ... is a commitment to 0')

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

namespace GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- Proof of Theorem 4, p. 13: on a perfectly binding key, if `V01(ck, c, π)` accepts then at least one of
`(c₁, c₂, c₃)` and `(c₁u⁻¹, c₂v⁻¹, c₃w⁻¹)` is a linear tuple with respect to `(f, h, g)`, and `c` or
`c · com(−1; 0, 0)` is a commitment to `0`. -/
theorem soundness_step (S : DLINSetup G GT) (ck : CommitKey G) (xk : ZMod S.p × ZMod S.p × ZMod S.p)
    (hck : S.IsBindingKey ck xk) (c : G × G × G) (π : Proof01 G) (hV : S.V01 ck c π) :
    (S.IsLinearTuple ck.f ck.h S.g c ∨
        S.IsLinearTuple ck.f ck.h S.g (c.1 * ck.u⁻¹, c.2.1 * ck.v⁻¹, c.2.2 * ck.w⁻¹)) ∧
      ((∃ r s : ZMod S.p, c = S.com ck 0 r s) ∨
        (∃ r s : ZMod S.p, c * S.com ck (-1) 0 0 = S.com ck 0 r s)) := by sorry

end GOSNIZK.DLINCommit
