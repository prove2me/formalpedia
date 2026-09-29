-- Prove2me | Theorems.Thm_MTT_distribution_relation
-- name    : MTT.distribution_relation
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-05T22:00:49.60667+00:00
-- url     : https://prove2.me/theorems/e07f94dc-21ef-44fc-b6df-d72bd0f0dc6b
-- title:
--   Compatibility of polynomial disk moments under refinement
-- statement:
--   For an ordinary root and any period system, each signed degree-j disk moment at positive depth n equals the sum of its p refinements at depth n+1. This holds for every integer center, both signs, and all 0 ≤ j ≤ k−2. The disk moments are defined by (10.2), with the correction term at depth n−1.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §10 Proposition, p. 12, with (10.2); §4 Proposition, (4.2), p. 8.

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.distribution_relation
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (s : Bool) (j : ℕ) (hj : j ≤ k - 2) (n : ℕ) (hn : 0 < n) (a : ℤ) :
    (∑ b ∈ Finset.range p,
      diskMoment f ιp P α s j (n + 1) (a + (b : ℤ) * (p : ℤ) ^ n)) =
      diskMoment f ιp P α s j n a := by sorry
