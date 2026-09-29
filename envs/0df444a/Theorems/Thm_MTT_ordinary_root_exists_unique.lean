-- Prove2me | Theorems.Thm_MTT_ordinary_root_exists_unique
-- name    : MTT.ordinary_root_exists_unique
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-05T22:00:13.823322+00:00
-- url     : https://prove2.me/theorems/ba0388ba-8d24-4ebd-86a9-990686c1ef3a
-- title:
--   Existence and uniqueness of the ordinary p-root
-- statement:
--   If the p-th eigenvalue is a p-adic unit, the polynomial X²−a_p X+ε(p)p^(k−1) has exactly one root of p-adic norm one. Characters and coefficients are transported through the fixed algebraic-to-p-adic embedding. This includes p dividing the level, where the constant term vanishes.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §12, p. 16, ordinary case; polynomial (10.1), p. 12.

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.ordinary_root_exists_unique
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (hord : ‖ιp (f.coeff p)‖ = 1) :
    ∃! α : ℂ_[p], IsOrdinaryRoot f ιp α := by sorry
