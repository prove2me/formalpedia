-- Prove2me | Theorems.Thm_IntMul_BinaryPhase_residual_normal_form
-- name    : IntMul.BinaryPhase.residual_normal_form
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T17:36:51.992361+00:00
-- url     : https://prove2.me/theorems/a865902e-7482-4dae-af89-3e3456d71004
-- title:
--   One-child normal form for every nondegenerate binary quadratic residual
-- statement:
--   Let $V$ be a finite binary vector space with basis indexed by a finite set $I$, let $B$ be a nondegenerate bilinear form on $V$, and let $q:V\to\mathbb Z/4\mathbb Z$ satisfy $q(0)=0$ and $q(z+w)=q(z)+q(w)+2B(z,w)$. Define
--   $$K(x,y)=2^{-|I|}\sum_{z\in V}i^{q(z)}(-1)^{B(z,x+y)}.$$
--   There are binary linear address isomorphisms $e_L,e_R:V\to\mathbb F_2^I$, a scalar $\varepsilon$ with $\varepsilon^4=1$, and diagonal phase functions $d_L,d_R$ whose values have fourth power one, such that
--   $$K(x,y)=\varepsilon\,d_L(x)\left(\prod_{j\in I}C(e_L(x)_j,e_R(y)_j)\right)d_R(y),$$
--   where $C$ has diagonal entry $(1+i)/2$ and off-diagonal entry $(1-i)/2$. Thus the residual kernel factors through exactly one rank-$|I|$ tensor child, two binary address changes, and fourth-root phase corrections. The address changes may differ, so alternating forms are included without an orthonormal-basis assumption. This is an exact algebraic kernel identity; implementing the address and phase passes on a fixed-tape machine is a separate task.
-- source:
--   CrocSwap/integer-mult-bounds, commit 3b6b66891c0ac888521cf591fe306c6286601d4f, notes/endpoint-gauge-complex.tex, subsection “A normal form for every nondegenerate binary residual”. https://github.com/CrocSwap/integer-mult-bounds/blob/3b6b66891c0ac888521cf591fe306c6286601d4f/notes/endpoint-gauge-complex.tex

import Definitions.Def_IntMul_BinaryQuadraticPhase
import Theorems.Thm_IntMul_BinaryPhase_residual_gauss_interface
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic
open scoped BigOperators
open IntMul.BinaryPhase

theorem IntMul.BinaryPhase.residual_normal_form
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ZMod 4) (hq0 : q 0 = 0)
    (hpolar : ∀ z w, q (z + w) = q z + q w + twice (B z w))
    (b : Module.Basis ι (ZMod 2) V) :
    ∃ (eL eR : V ≃ₗ[ZMod 2] (ι → ZMod 2)) (ε : ℂ) (dL dR : V → ℂ),
      ε ^ 4 = 1 ∧ (∀ x, dL x ^ 4 = 1) ∧ (∀ y, dR y ^ 4 = 1) ∧
      ∀ x y,
        (∑ z : V, (phase (q z) : ℂ) * sign (B z (x + y))) /
          (2 : ℂ) ^ Fintype.card ι =
        ε * dL x * tensorKernel (eL x) (eR y) * dR y := by sorry
