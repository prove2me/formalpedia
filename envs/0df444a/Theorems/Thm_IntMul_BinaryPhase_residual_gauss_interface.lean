-- Prove2me | Theorems.Thm_IntMul_BinaryPhase_residual_gauss_interface
-- name    : IntMul.BinaryPhase.residual_gauss_interface
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T17:29:41.861759+00:00
-- url     : https://prove2.me/theorems/4ea17f94-d967-4a75-976a-d8d1ec89df6a
-- title:
--   Nondegenerate binary quadratic Gauss-sum and kernel interface
-- statement:
--   Let $V$ be a finite vector space over $\mathbb F_2$, let $B$ be a nondegenerate bilinear form, and let $q:V\to\mathbb Z/4\mathbb Z$ satisfy $q(0)=0$ and $q(z+w)=q(z)+q(w)+2B(z,w)$. Put $S_q=\sum_{z\in V}i^{q(z)}$ and $r=\dim_{\mathbb F_2}V$. Then the exact Gaussian norm is $N(S_q)=|V|=2^r$, the normalized scalar $S_q((1-i)/2)^r$ is a fourth root of unity, and
--   $$\sum_z i^{q(z)}(-1)^{B(z,x+y)}=S_q i^{-q(x)}(-1)^{B(x,y)}i^{-q(y)}.$$
--   This covers alternating and nonalternating polar forms without requiring an orthonormal basis. It is the Gauss-sum and completing-square component of the complex residual normal form used in the integer-multiplication κ construction; the tensor child factorization and the machine realization are separate obligations.
-- source:
--   CrocSwap/integer-mult-bounds, commit 3b6b66891c0ac888521cf591fe306c6286601d4f, notes/endpoint-gauge-complex.tex, subsection “A normal form for every nondegenerate binary residual”, assertion that S_q b^r is a fourth root of unity. https://github.com/CrocSwap/integer-mult-bounds/blob/3b6b66891c0ac888521cf591fe306c6286601d4f/notes/endpoint-gauge-complex.tex . This is an alternative arithmetic proof of the scalar step using divisibility by 1+i, rather than quadratic-form block classification.

import Definitions.Def_IntMul_BinaryQuadraticPhase
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic
open scoped BigOperators

theorem IntMul.BinaryPhase.residual_gauss_interface
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ZMod 4) (hq0 : q 0 = 0)
    (hpolar : ∀ z w, q (z + w) = q z + q w + IntMul.BinaryPhase.twice (B z w)) :
    (∑ z : V, IntMul.BinaryPhase.phase (q z)).norm = (Fintype.card V : ℤ) ∧
    (((∑ z : V, IntMul.BinaryPhase.phase (q z) : GaussianInt) : ℂ) *
      ((1 - Complex.I) / 2) ^ Module.finrank (ZMod 2) V) ^ 4 = 1 ∧
    ∀ x y : V,
      (∑ z : V, (IntMul.BinaryPhase.phase (q z) : ℂ) * IntMul.BinaryPhase.sign (B z (x + y))) =
        (∑ z : V, (IntMul.BinaryPhase.phase (q z) : ℂ)) *
          (IntMul.BinaryPhase.phase (q x) : ℂ)⁻¹ * IntMul.BinaryPhase.sign (B x y) *
            (IntMul.BinaryPhase.phase (q y) : ℂ)⁻¹ := by sorry
