-- Prove2me | Theorems.Thm_HodgeComputer_Formal_HoldoutCover_irreducible_power_add_constant
-- name    : HodgeComputer.Formal.HoldoutCover.irreducible_power_add_constant
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:18:09.062984+00:00
-- url     : https://prove2.me/theorems/742c087e-dc0b-45f3-930d-d7c6ae2f7dbe
-- title:
--   Eisenstein irreducibility of $Y^d + a(X)$
-- statement:
--   Let $k$ be a field and $a \in k[X]$ a polynomial with $a(0) = 0$ and $a'(0) \neq 0$ (i.e., $a$ vanishes to exact order $1$ at $0$). Then for every integer $d \ge 1$, the bivariate polynomial
--
--   $$Y^d + a(X) \in (k[X])[Y]$$
--
--   is irreducible over $k[X]$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/HoldoutCover/HypersurfaceDomain.lean#L16-L197

import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
set_option autoImplicit false
open scoped Polynomial

theorem HodgeComputer.Formal.HoldoutCover.irreducible_power_add_constant
    {k : Type*} [Field k] (a : k[X]) (ha0 : a.coeff 0 = 0)
    (ha1 : a.coeff 1 ≠ 0) (d : ℕ) (hd : 1 ≤ d) :
    Irreducible (Polynomial.X ^ d + Polynomial.C a : (k[X])[X]) := by sorry
