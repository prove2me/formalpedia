-- Prove2me | Theorems.Thm_MTT_exists_ordinary_padic_L_measure
-- name    : MTT.exists_ordinary_padic_L_measure
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-05T22:02:04.005731+00:00
-- url     : https://prove2.me/theorems/f8acca81-a159-455e-96c5-3e67cf7cd5e3
-- title:
--   Existence of the ordinary p-adic L-measure with MTT interpolation
-- statement:
--   For every prime p, positive level N, weight k ≥ 2, normalized algebraic cuspidal Hecke eigenform f of nebentypus ε, and fixed embeddings of the algebraic closure of Q into C and Cp, assume the p-th eigenvalue is a p-adic unit. There exist a unit root α, a pair of nonzero periods with algebraic normalized modular integrals spanning a finite integral lattice, and a bounded Cp-valued measure on Zp*. For every primitive χ of conductor p^n and every 0 ≤ j ≤ k−2, its χ(x)x^j moment is the MTT Euler multiplier times the algebraic image of p^(n(j+1)) j! L(f_{χ⁻¹},j+1)/((−2πi)^j τ(χ⁻¹) Ω^{χ(−1)(−1)^j}). The complex L-value is defined by its actual Mellin integral. The quantifiers include n=0, p=2, and p dividing N.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §11 Theorem and §14 Proposition, pp. 13–16 and 20–21, in the ordinary case; scalar period normalization uses Manin–Shimura rationality.

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.exists_ordinary_padic_L_measure
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (hord : ‖ιp (f.coeff p)‖ = 1) :
    ∃ (α : ℂ_[p]) (P : Periods k ι f.form) (μ : UnitMeasure p),
      IsOrdinaryRoot f ιp α ∧ Interpolates f ιp P.omega α μ := by sorry
