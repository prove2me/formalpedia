-- Prove2me | Theorems.Thm_IsReduced_padic_tensorProduct_of_moduleFinite_int
-- name    : IsReduced.padic_tensorProduct_of_moduleFinite_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/7d2294c5-3ea0-50f4-98ca-2b774f96e69f
-- title:
--   Base change to ℚ_ℓ preserves reducedness over ℤ
-- statement:
--   Let $S$ be a commutative ring which is finite and free as a $\mathbf{Z}$-module and reduced (its only nilpotent element is $0$), and let $\ell$ be a prime number. Then the $\mathbf{Z}$-module tensor product $\mathbf{Q}_\ell \otimes_{\mathbf{Z}} S$, carrying its induced commutative ring structure, is reduced.
--
--   This is the statement that a reduced order-like $\mathbf{Z}$-algebra of finite rank remains reduced after base change to the $\ell$-adic numbers, the point being that a reduced finite $\mathbf{Q}$-algebra is étale because $\mathbf{Q}$ is perfect. It is used to establish that the rational Hecke algebra of a modular curve stays reduced after $\ell$-adic base change, in [`ModularCurve.isReduced_rationalHeckeAlgebra`](thm.html#ModularCurve.isReduced_rationalHeckeAlgebra).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsReduced_padic_tensorProduct_of_moduleFinite_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsReduced.padic_tensorProduct_of_moduleFinite_int
    (S : Type*) [CommRing S] [Module.Finite ℤ S] [Module.Free ℤ S] [IsReduced S] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsReduced (TensorProduct ℤ ℚ_[ℓ] S) := by sorry
