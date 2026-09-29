-- Prove2me | Theorems.Thm_MTT_birch_mellin_formula
-- name    : MTT.birch_mellin_formula
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-05T22:00:33.077088+00:00
-- url     : https://prove2.me/theorems/d9661d44-2612-4ab4-82e1-b5e2af1afc5f
-- title:
--   Birch–Mellin formula for primitive twists
-- statement:
--   For any primitive Dirichlet character χ of positive conductor m and any 0 ≤ j ≤ k−2, the Mellin critical value of the inverse-character twist equals ((−2πi)^j τ(χ⁻¹)/(j! m^(j+1))) times the χ-weighted sum of the modular symbols λ(f,X^j;a,m). The modular symbols and Mellin integral are the actual complex integrals, and the Gauss sum uses the positive exponential.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §7 and (8.6), pp. 9–10; finite-translate twist (8.3).

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.birch_mellin_formula
    {N k m : ℕ} [NeZero m] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι)
    (χ : DirichletCharacter Qbar m) (hχ : χ.IsPrimitive)
    (j : ℕ) (hj : j ≤ k - 2) :
    criticalLValue ι f.form m χ j =
      ((-2 * Real.pi * Complex.I) ^ j * gaussSum ι m χ⁻¹ /
        ((j.factorial : ℂ) * (m : ℂ) ^ (j + 1))) *
        ∑ a : ZMod m, ι (χ a) * modularSymbol f.form j a.val m := by sorry
