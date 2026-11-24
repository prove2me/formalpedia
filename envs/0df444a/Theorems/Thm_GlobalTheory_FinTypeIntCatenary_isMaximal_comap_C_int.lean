-- Prove2me | Theorems.Thm_GlobalTheory_FinTypeIntCatenary_isMaximal_comap_C_int
-- name    : GlobalTheory.FinTypeIntCatenary.isMaximal_comap_C_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:55.668808+00:00
-- url     : https://prove2.me/theorems/0671dc91-e628-45a9-9d65-ea14d622ee29
-- title:
--   Fin Type Int Catenary: is Maximal comap C int
-- statement:
--   The Fin Type Int Catenary construction uses the is Maximal comap C int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDim.lean#L74-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinTypeIntCatenary
open ReciprocityTheory.CA

theorem GlobalTheory.FinTypeIntCatenary.isMaximal_comap_C_int (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ)).IsMaximal := by sorry
