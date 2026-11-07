-- Prove2me | Theorems.Thm_LineVsPoint_lemma_2_2
-- name    : LineVsPoint.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:03:51.265554+00:00
-- url     : https://prove2.me/theorems/de1902d4-6f0f-48a8-87da-f80224b59849
-- title:
--   Lemma 2.2 — $\dim V_D > D^3/(6d)$
-- statement:
--   **Lemma 2.2.** Let $\mathbb F$ be a field and give $X,Y,Z$ the weights $1,1,d$. For every $D\ge 0$ and $d\ge 1$, the space $V_D$ of polynomials in $\mathbb F[X,Y,Z]$ of weighted degree at most $D$ satisfies
--
--   $$
--   \dim V_D>\frac{D^3}{6d}.
--   $$
--
--   Equivalently, more than $D^3/(6d)$ monomials $X^iY^jZ^k$ have $i+j+dk\le D$. With $D=\lceil 4(dq^2)^{1/3}\rceil$ this gives $\dim V_D>q^2$, which is what makes the interpolation of Lemma 3.2 possible.
--
--   Differences from the source:
--   - reading: every D ≥ 0 (integrality not specified) → every real D ≥ 0, with V_D spanned by the monomials of weighted degree ≤ D; reason: the stronger of the two readings; it contains the integer case
--   - generalization: F_q → any field F; reason: the dimension of V_D is the monomial count, which does not depend on the field, and F_q is the special case of a finite field
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 2.2, p.11

import Definitions.Def_LineVsPoint_VD

set_option autoImplicit false

universe u

namespace LineVsPoint

/-- **Lemma 2.2** (monomial count). *For every `D ≥ 0` and `d ≥ 1`, `dim V_D > D³/(6d)`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Lemma 2.2, p.11.

**Formalization Note.** `V_D` is the span of the monomials `X^i Y^j Z^k` with `i + j + dk ≤ D`
over any field; `D` is any real number `≥ 0` (the paper does not say whether `D` is an integer;
the real reading contains the integer one). -/
theorem lemma_2_2 :
    ∀ (F : Type u) [Field F] (d : ℕ), 1 ≤ d → ∀ D : ℝ, 0 ≤ D →
      D ^ 3 / (6 * (d : ℝ)) < (Module.finrank F (VD F d D) : ℝ) := by sorry

end LineVsPoint
