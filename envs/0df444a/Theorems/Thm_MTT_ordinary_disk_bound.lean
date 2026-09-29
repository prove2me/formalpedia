-- Prove2me | Theorems.Thm_MTT_ordinary_disk_bound
-- name    : MTT.ordinary_disk_bound
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-05T22:01:08.267758+00:00
-- url     : https://prove2.me/theorems/4b2d9616-353a-4f3d-893b-974b8572c530
-- title:
--   Uniform boundedness of ordinary disk masses
-- statement:
--   For a fixed ordinary form, period system, and unit root, there is one nonnegative real constant bounding the p-adic norm of every signed constant disk mass, uniformly over all positive depths and all integer centers. The finite integral lattice and the unit-root hypothesis are retained explicitly.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §11, axiom III at polynomial degree zero, pp. 13–15, specialized to ord_p(α)=0; §2 finite generation, pp. 6–7, and (10.2).

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.ordinary_disk_bound
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Bool) (n : ℕ), 0 < n → ∀ (a : ℤ),
      ‖diskMoment f ιp P α s 0 n a‖ ≤ C := by sorry
