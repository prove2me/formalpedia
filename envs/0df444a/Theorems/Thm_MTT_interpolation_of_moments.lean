-- Prove2me | Theorems.Thm_MTT_interpolation_of_moments
-- name    : MTT.interpolation_of_moments
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-05T22:01:50.491266+00:00
-- url     : https://prove2.me/theorems/c3f324df-83ea-4494-b244-0d3669dd1f39
-- title:
--   MTT interpolation from the two signed moment measures
-- statement:
--   If the two signed bounded measures realize every prescribed critical polynomial disk moment, their sum satisfies the full scalar period-normalized MTT interpolation identity for every primitive p-power-conductor character and critical exponent. The conductor-one case retains both Euler factors; positive conductor has multiplier α^(−n). Algebraic values bridge the two fixed embeddings.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §14 Proposition, pp. 20–21, applied to the two signed period-normalized components; (8.6) and (10.2).

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.interpolation_of_moments
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (μ : Bool → UnitMeasure p)
    (hμ : ∀ s, RealizesMoments f ιp P α s (μ s)) :
    Interpolates f ιp P.omega α (μ true + μ false) := by sorry
