-- Prove2me | Theorems.Thm_MTT_periods_exist
-- name    : MTT.periods_exist
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-05T21:59:46.118011+00:00
-- url     : https://prove2.me/theorems/5a99c269-14ef-4eaf-868f-3178fd0b9e23
-- title:
--   Signed algebraic periods and a finite integral lattice
-- statement:
--   Every normalized algebraic cuspidal Hecke eigenform of positive level and weight k ≥ 2 has two nonzero complex periods. Dividing each signed modular integral by the corresponding period gives algebraic values; their integral span, for all rational cusps and degrees 0 through k−2, is finitely generated. The signed projection includes one half and reflection of the polynomial.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §2 Proposition, pp. 6–7, together with Manin–Shimura period rationality; Shimura, On the periods of modular forms (1977), https://doi.org/10.1007/BF01391466. For the general-eigenform reduction see Williams, An introduction to p-adic L-functions II, Proposition 11.21, https://warwick.ac.uk/fac/sci/maths/people/staff/cwilliams/lecturenotes/lecture_notes_part_ii.pdf. This milestone combines rationality and finite generation, rather than attributing both to a single proposition.

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem MTT.periods_exist
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    Nonempty (MTT.Periods k ι f.form) := by sorry
