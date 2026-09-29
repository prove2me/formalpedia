-- Prove2me | Theorems.Thm_MTT_measure_extension
-- name    : MTT.measure_extension
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-05T22:01:21.843709+00:00
-- url     : https://prove2.me/theorems/ede62bad-efd1-46eb-b41d-ba9cf5f2a802
-- title:
--   Unique bounded measure realizing the critical polynomial moments
-- statement:
--   For each sign and each ordinary root, the prescribed disk moments extend to exactly one continuous Cp-linear functional on C(Zp*,Cp). On every unit residue disk of positive depth, this measure integrates X^j to the prescribed moment for every 0 ≤ j ≤ k−2. The assertion also supplies the continuous disk test functions pointwise, rather than assuming their existence.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §11 Theorem (Vishik, Amice–Vélu), pp. 13–16, ordinary specialization and bounded extension from locally analytic to continuous test functions.

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.measure_extension
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (s : Bool) :
    ∃! μ : UnitMeasure p, RealizesMoments f ιp P α s μ := by sorry
